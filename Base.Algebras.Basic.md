---
layout: default
title : "Base.Algebras.Basic module (Agda Universal Algebra Library)"
date : "2021-04-23"
author: "agda-algebras development team"
---

### <a id="basic-definitions">Basic definitions</a>

This is the [Base.Algebras.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="311" class="Symbol">{-#</a> <a id="315" class="Keyword">OPTIONS</a> <a id="323" class="Pragma">--without-K</a> <a id="335" class="Pragma">--exact-split</a> <a id="349" class="Pragma">--safe</a> <a id="356" class="Symbol">#-}</a>

<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="Overture.html" class="Module">Overture</a> <a id="382" class="Keyword">using</a> <a id="388" class="Symbol">(</a> <a id="390" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="392" class="Symbol">;</a> <a id="394" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="396" class="Symbol">;</a> <a id="398" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="408" class="Symbol">)</a>

<a id="411" class="Keyword">module</a> <a id="418" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="438" class="Symbol">{</a><a id="439" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="441" class="Symbol">:</a> <a id="443" href="Overture.Signatures.html#3264" class="Function">Signature</a> <a id="453" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="455" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="457" class="Symbol">}</a> <a id="459" class="Keyword">where</a>

<a id="466" class="Comment">-- Imports from the Agda (Builtin) and the Agda Standard Library --------------</a>
<a id="546" class="Keyword">open</a> <a id="551" class="Keyword">import</a> <a id="558" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="575" class="Keyword">using</a> <a id="581" class="Symbol">()</a> <a id="584" class="Keyword">renaming</a> <a id="593" class="Symbol">(</a> <a id="595" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="599" class="Symbol">to</a>  <a id="603" class="Primitive">Type</a> <a id="608" class="Symbol">;</a> <a id="610" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="616" class="Symbol">to</a> <a id="619" class="Primitive">ℓ₀</a> <a id="622" class="Symbol">)</a>
<a id="624" class="Keyword">open</a> <a id="629" class="Keyword">import</a> <a id="636" href="Data.Product.html" class="Module">Data.Product</a>     <a id="653" class="Keyword">using</a> <a id="659" class="Symbol">(</a> <a id="661" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="665" class="Symbol">;</a> <a id="667" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="671" class="Symbol">;</a> <a id="673" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="682" class="Symbol">)</a>
<a id="684" class="Keyword">open</a> <a id="689" class="Keyword">import</a> <a id="696" href="Level.html" class="Module">Level</a>            <a id="713" class="Keyword">using</a> <a id="719" class="Symbol">(</a> <a id="721" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="727" class="Symbol">;</a> <a id="729" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="733" class="Symbol">;</a> <a id="735" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="739" class="Symbol">)</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="770" class="Keyword">using</a> <a id="776" class="Symbol">(</a> <a id="778" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="792" class="Symbol">)</a> <a id="794" class="Keyword">renaming</a> <a id="803" class="Symbol">(</a> <a id="805" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="809" class="Symbol">to</a> <a id="812" class="Function">BinRel</a> <a id="819" class="Symbol">)</a>
<a id="821" class="Keyword">open</a> <a id="826" class="Keyword">import</a> <a id="833" href="Relation.Unary.html" class="Module">Relation.Unary</a>   <a id="850" class="Keyword">using</a> <a id="856" class="Symbol">(</a> <a id="858" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="862" class="Symbol">;</a> <a id="864" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="869" class="Symbol">)</a>


<a id="873" class="Comment">-- Imports from the Agda Universal Algebra Library ----------------------------</a>
<a id="953" class="Keyword">open</a>  <a id="959" class="Keyword">import</a> <a id="966" href="Overture.html" class="Module">Overture</a>        <a id="982" class="Keyword">using</a> <a id="988" class="Symbol">(</a> <a id="990" href="Overture.Basic.html#4326" class="Function Operator">∣_∣</a> <a id="994" class="Symbol">;</a> <a id="996" href="Overture.Basic.html#4364" class="Function Operator">∥_∥</a> <a id="1000" class="Symbol">;</a> <a id="1002" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="1005" class="Symbol">)</a>
<a id="1007" class="Keyword">open</a>  <a id="1013" class="Keyword">import</a> <a id="1020" href="Base.Relations.html" class="Module">Base.Relations</a>  <a id="1036" class="Keyword">using</a> <a id="1042" class="Symbol">(</a> <a id="1044" href="Base.Relations.Discrete.html#6787" class="Function Operator">_|:_</a> <a id="1049" class="Symbol">;</a> <a id="1051" href="Base.Relations.Discrete.html#7103" class="Function Operator">_|:pred_</a> <a id="1060" class="Symbol">;</a> <a id="1062" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="1066" class="Symbol">;</a> <a id="1068" href="Base.Relations.Continuous.html#5603" class="Function">compatible-Rel</a> <a id="1083" class="Symbol">)</a>
                             <a id="1114" class="Keyword">using</a> <a id="1120" class="Symbol">(</a> <a id="1122" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="1126" class="Symbol">;</a> <a id="1128" href="Base.Relations.Continuous.html#6317" class="Function">compatible-REL</a> <a id="1143" class="Symbol">)</a>

<a id="1146" class="Keyword">private</a> <a id="1154" class="Keyword">variable</a> <a id="1163" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="1165" href="Base.Algebras.Basic.html#1165" class="Generalizable">β</a> <a id="1167" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a> <a id="1169" class="Symbol">:</a> <a id="1171" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>


#### <a id="algebras">Algebras</a>

Our first goal is to develop a working vocabulary and formal library for classical
(single-sorted, set-based) universal algebra.  In this section we define the main
objects of study.  An *algebraic structure* (or *algebra*) in the signature
`𝑆 = (𝐹, ρ)` is denoted by `𝑨 = (A, Fᴬ)` and consists of

*  `A` := a *nonempty* set (or type), called the *domain* (or *carrier* or
   *universe*) of the algebra;
*  `Fᴬ := { fᴬ ∣ f ∈ F, : (ρf → A) → A }`, a collection of *operations* on `𝑨`;
*  a (potentially empty) collection of *identities* satisfied by elements and
   *operations of `𝑨`.

Note that to each operation symbol `f ∈ 𝐹` corresponds an operation
`fᴬ` on `𝑨` of arity `ρf`; we call such `fᴬ` the *interpretation* of the symbol
`f` in the algebra `𝑨`. We call an algebra in the signature `𝑆` an `𝑆`-*algebra*.
An algebra is called *finite* if it has a finite domain, and is called *trivial*
if its universe is a singleton.  Given two algebras `𝑨` and `𝑩`, we say that `𝑩`
is a *reduct* of `𝑨` if both algebras have the same domain and `𝑩` can be obtained
from `𝑨` by simply removing some of the operations.

Recall, we defined the type `Signature 𝓞 𝓥` above as the dependent pair type
`Σ F ꞉ Type 𝓞 , (F → Type 𝓥)`, and the type `Op` of operation symbols is the
function type `Op I A = (I → A) → A` (see [Base.Relations.Discrete][]).

For a fixed signature `𝑆 : Signature 𝓞 𝓥` and universe level `α`, we define the
*type of algebras in the signature* `𝑆` (or *type of* `𝑆`-*algebras*) *with domain
type* `Type α` as follows.

<pre class="Agda">

<a id="Algebra"></a><a id="2774" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="2782" class="Symbol">:</a> <a id="2784" class="Symbol">(</a><a id="2785" href="Base.Algebras.Basic.html#2785" class="Bound">α</a> <a id="2787" class="Symbol">:</a> <a id="2789" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="2794" class="Symbol">)</a> <a id="2796" class="Symbol">→</a> <a id="2798" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="2803" class="Symbol">(</a><a id="2804" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="2806" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2808" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="2810" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="2812" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="2816" href="Base.Algebras.Basic.html#2785" class="Bound">α</a><a id="2817" class="Symbol">)</a>
<a id="2819" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="2827" href="Base.Algebras.Basic.html#2827" class="Bound">α</a> <a id="2829" class="Symbol">=</a>  <a id="2832" href="Data.Product.html#916" class="Function">Σ[</a> <a id="2835" href="Base.Algebras.Basic.html#2835" class="Bound">A</a> <a id="2837" href="Data.Product.html#916" class="Function">∈</a> <a id="2839" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="2844" href="Base.Algebras.Basic.html#2827" class="Bound">α</a> <a id="2846" href="Data.Product.html#916" class="Function">]</a>                 <a id="2864" class="Comment">-- the domain</a>
             <a id="2891" class="Symbol">∀</a> <a id="2893" class="Symbol">(</a><a id="2894" href="Base.Algebras.Basic.html#2894" class="Bound">f</a> <a id="2896" class="Symbol">:</a> <a id="2898" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="2900" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="2902" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="2903" class="Symbol">)</a> <a id="2905" class="Symbol">→</a> <a id="2907" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="2910" href="Base.Algebras.Basic.html#2835" class="Bound">A</a> <a id="2912" class="Symbol">(</a><a id="2913" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="2915" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="2917" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="2919" href="Base.Algebras.Basic.html#2894" class="Bound">f</a><a id="2920" class="Symbol">)</a>  <a id="2923" class="Comment">-- the basic operations</a>

</pre>

It would be more precise to refer to inhabitants of this type as ∞-*algebras*
because their domains can be of arbitrary type and need not be truncated at some
level and, in particular, need to be a set. (See [Base.Equality.Truncation][].)

We might take this opportunity to define the type of 0-*algebras*, that is,
algebras whose domains are sets, which is probably closer to what most of us think
of when doing informal universal algebra.  However, in the
[agda-algebras](https://github.com/ualib/agda-algebras) library we will only need
to know that the domains of certain algebras are sets in a few places, so it seems
preferable to work with general (∞-)algebras throughout and then explicitly
postulate additional axioms (e.g., [uniquness of identity
proofs](https://ualib.github.io/agda-algebras/Equality.Truncation.html#uniqueness-of-identity-proofs)
if and only if necessary.


#### <a id="algebras-as-record-types">Algebras as record types</a>

A popular way to represent algebraic structures in type theory is with record
types.  The Sigma type defined above provides an equivalent alternative that we
happen to prefer and we use it throughout the library, both for consistency and
because of its direct connection to the existential quantifier of logic. Recall
that the type `Σ x ꞉ X , P x` represents the proposition, "there exists `x` in `X`
such that `P x` holds;" in symbols, `∃ x ∈ X , P x`.  Indeed, an inhabitant of `Σ
x ꞉ X , P x` is a pair `(x , p)` such that `x` inhabits `X` and `p` is a proof of
`P x`. In other terms, the pair `(x , p)` is a witness and proof of the
proposition `∃ x ∈ X , P x`.

Nonetheless, for those who prefer to represent algebraic structures in type theory
using records, we offer the following definition (which is equivalent to the Sigma
type formulation).

<pre class="Agda">

<a id="4782" class="Keyword">record</a> <a id="algebra"></a><a id="4789" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="4797" class="Symbol">(</a><a id="4798" href="Base.Algebras.Basic.html#4798" class="Bound">α</a> <a id="4800" class="Symbol">:</a> <a id="4802" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4807" class="Symbol">)</a> <a id="4809" class="Symbol">:</a> <a id="4811" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a><a id="4815" class="Symbol">(</a><a id="4816" href="Agda.Primitive.html#780" class="Primitive">suc</a><a id="4819" class="Symbol">(</a><a id="4820" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="4822" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4824" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="4826" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4828" href="Base.Algebras.Basic.html#4798" class="Bound">α</a><a id="4829" class="Symbol">))</a> <a id="4832" class="Keyword">where</a>
 <a id="4839" class="Keyword">constructor</a> <a id="mkalg"></a><a id="4851" href="Base.Algebras.Basic.html#4851" class="InductiveConstructor">mkalg</a>
 <a id="4858" class="Keyword">field</a>
  <a id="algebra.carrier"></a><a id="4866" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a> <a id="4874" class="Symbol">:</a> <a id="4876" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="4881" href="Base.Algebras.Basic.html#4798" class="Bound">α</a>
  <a id="algebra.opsymbol"></a><a id="4885" href="Base.Algebras.Basic.html#4885" class="Field">opsymbol</a> <a id="4894" class="Symbol">:</a> <a id="4896" class="Symbol">(</a><a id="4897" href="Base.Algebras.Basic.html#4897" class="Bound">f</a> <a id="4899" class="Symbol">:</a> <a id="4901" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="4903" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="4905" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="4906" class="Symbol">)</a> <a id="4908" class="Symbol">→</a> <a id="4910" class="Symbol">((</a><a id="4912" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="4914" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="4916" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="4918" href="Base.Algebras.Basic.html#4897" class="Bound">f</a><a id="4919" class="Symbol">)</a> <a id="4921" class="Symbol">→</a> <a id="4923" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a><a id="4930" class="Symbol">)</a> <a id="4932" class="Symbol">→</a> <a id="4934" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a>

</pre>

This representation of algebras as inhabitants of a record type is equivalent to
the representation using Sigma types in the sense that a bi-implication between
the two representations is obvious.

<pre class="Agda">

<a id="5167" class="Keyword">open</a> <a id="5172" href="Base.Algebras.Basic.html#4789" class="Module">algebra</a>

<a id="algebra→Algebra"></a><a id="5181" href="Base.Algebras.Basic.html#5181" class="Function">algebra→Algebra</a> <a id="5197" class="Symbol">:</a> <a id="5199" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="5207" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="5209" class="Symbol">→</a> <a id="5211" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="5219" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a>
<a id="5221" href="Base.Algebras.Basic.html#5181" class="Function">algebra→Algebra</a> <a id="5237" href="Base.Algebras.Basic.html#5237" class="Bound">𝑨</a> <a id="5239" class="Symbol">=</a> <a id="5241" class="Symbol">(</a><a id="5242" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a> <a id="5250" href="Base.Algebras.Basic.html#5237" class="Bound">𝑨</a> <a id="5252" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5254" href="Base.Algebras.Basic.html#4885" class="Field">opsymbol</a> <a id="5263" href="Base.Algebras.Basic.html#5237" class="Bound">𝑨</a><a id="5264" class="Symbol">)</a>

<a id="Algebra→algebra"></a><a id="5267" href="Base.Algebras.Basic.html#5267" class="Function">Algebra→algebra</a> <a id="5283" class="Symbol">:</a> <a id="5285" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="5293" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="5295" class="Symbol">→</a> <a id="5297" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="5305" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a>
<a id="5307" href="Base.Algebras.Basic.html#5267" class="Function">Algebra→algebra</a> <a id="5323" href="Base.Algebras.Basic.html#5323" class="Bound">𝑨</a> <a id="5325" class="Symbol">=</a> <a id="5327" href="Base.Algebras.Basic.html#4851" class="InductiveConstructor">mkalg</a> <a id="5333" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5335" href="Base.Algebras.Basic.html#5323" class="Bound">𝑨</a> <a id="5337" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5339" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="5341" href="Base.Algebras.Basic.html#5323" class="Bound">𝑨</a> <a id="5343" href="Overture.Basic.html#4364" class="Function Operator">∥</a>
</pre>


#### <a id="operation-interpretation-syntax">Operation interpretation syntax</a>

We now define a convenient shorthand for the interpretation of an operation symbol.
This looks more similar to the standard notation one finds in the literature as
compared to the double bar notation we started with, so we will use this new notation
almost exclusively in the remaining modules of the [agda-algebras][] library.

<pre class="Agda">

<a id="_̂_"></a><a id="5783" href="Base.Algebras.Basic.html#5783" class="Function Operator">_̂_</a> <a id="5787" class="Symbol">:</a> <a id="5789" class="Symbol">(</a><a id="5790" href="Base.Algebras.Basic.html#5790" class="Bound">𝑓</a> <a id="5792" class="Symbol">:</a> <a id="5794" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5796" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="5798" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="5799" class="Symbol">)(</a><a id="5801" href="Base.Algebras.Basic.html#5801" class="Bound">𝑨</a> <a id="5803" class="Symbol">:</a> <a id="5805" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="5813" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="5814" class="Symbol">)</a> <a id="5816" class="Symbol">→</a> <a id="5818" class="Symbol">(</a><a id="5819" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="5821" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="5823" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="5825" href="Base.Algebras.Basic.html#5790" class="Bound">𝑓</a>  <a id="5828" class="Symbol">→</a>  <a id="5831" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5833" href="Base.Algebras.Basic.html#5801" class="Bound">𝑨</a> <a id="5835" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="5836" class="Symbol">)</a> <a id="5838" class="Symbol">→</a> <a id="5840" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="5842" href="Base.Algebras.Basic.html#5801" class="Bound">𝑨</a> <a id="5844" href="Overture.Basic.html#4326" class="Function Operator">∣</a>
<a id="5846" href="Base.Algebras.Basic.html#5846" class="Bound">𝑓</a> <a id="5848" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="5850" href="Base.Algebras.Basic.html#5850" class="Bound">𝑨</a> <a id="5852" class="Symbol">=</a> <a id="5854" class="Symbol">λ</a> <a id="5856" href="Base.Algebras.Basic.html#5856" class="Bound">𝑎</a> <a id="5858" class="Symbol">→</a> <a id="5860" class="Symbol">(</a><a id="5861" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="5863" href="Base.Algebras.Basic.html#5850" class="Bound">𝑨</a> <a id="5865" href="Overture.Basic.html#4364" class="Function Operator">∥</a> <a id="5867" href="Base.Algebras.Basic.html#5846" class="Bound">𝑓</a><a id="5868" class="Symbol">)</a> <a id="5870" href="Base.Algebras.Basic.html#5856" class="Bound">𝑎</a>

</pre>

So, if `𝑓 : ∣ 𝑆 ∣` is an operation symbol in the signature `𝑆`, and if
`𝑎 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣` is a tuple of the appropriate arity, then `(𝑓 ̂ 𝑨) 𝑎`
denotes the operation `𝑓` interpreted in `𝑨` and evaluated at `𝑎`.

#### <a id="the-universe-level-of-an-algebra">The universe level of an algebra</a>

Occasionally we will be given an algebra and we just need to know the universe
level of its domain. The following utility function provides this.

<pre class="Agda">

<a id="Level-of-Alg"></a><a id="6345" href="Base.Algebras.Basic.html#6345" class="Function">Level-of-Alg</a> <a id="6358" class="Symbol">:</a> <a id="6360" class="Symbol">{</a><a id="6361" href="Base.Algebras.Basic.html#6361" class="Bound">α</a> <a id="6363" class="Symbol">:</a> <a id="6365" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="6370" class="Symbol">}</a> <a id="6372" class="Symbol">→</a> <a id="6374" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="6382" href="Base.Algebras.Basic.html#6361" class="Bound">α</a> <a id="6384" class="Symbol">→</a> <a id="6386" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="6392" href="Base.Algebras.Basic.html#6345" class="Function">Level-of-Alg</a> <a id="6405" class="Symbol">{</a><a id="6406" class="Argument">α</a> <a id="6408" class="Symbol">=</a> <a id="6410" href="Base.Algebras.Basic.html#6410" class="Bound">α</a><a id="6411" class="Symbol">}</a> <a id="6413" class="Symbol">_</a> <a id="6415" class="Symbol">=</a> <a id="6417" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="6419" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6421" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="6423" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6425" href="Agda.Primitive.html#780" class="Primitive">suc</a> <a id="6429" href="Base.Algebras.Basic.html#6410" class="Bound">α</a>

<a id="Level-of-Carrier"></a><a id="6432" href="Base.Algebras.Basic.html#6432" class="Function">Level-of-Carrier</a> <a id="6449" class="Symbol">:</a> <a id="6451" class="Symbol">{</a><a id="6452" href="Base.Algebras.Basic.html#6452" class="Bound">α</a>  <a id="6455" class="Symbol">:</a> <a id="6457" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="6462" class="Symbol">}</a> <a id="6464" class="Symbol">→</a> <a id="6466" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="6474" href="Base.Algebras.Basic.html#6452" class="Bound">α</a> <a id="6476" class="Symbol">→</a> <a id="6478" href="Agda.Primitive.html#597" class="Postulate">Level</a>
<a id="6484" href="Base.Algebras.Basic.html#6432" class="Function">Level-of-Carrier</a> <a id="6501" class="Symbol">{</a><a id="6502" class="Argument">α</a> <a id="6504" class="Symbol">=</a> <a id="6506" href="Base.Algebras.Basic.html#6506" class="Bound">α</a><a id="6507" class="Symbol">}</a> <a id="6509" class="Symbol">_</a> <a id="6511" class="Symbol">=</a> <a id="6513" href="Base.Algebras.Basic.html#6506" class="Bound">α</a>
</pre>


#### <a id="lifts-of-algebras">Level lifting algebra types</a>

Recall, in the [section on level lifting and
lowering](Functions.Lifts.html#level-lifting-and-lowering), we described the
difficulties one may encounter when working with a noncumulative universe
hierarchy. We made a promise to provide some domain-specific level lifting and
level lowering methods. Here we fulfill this promise by supplying a couple of
bespoke tools designed specifically for our operation and algebra types.

<pre class="Agda">

<a id="7033" class="Keyword">open</a> <a id="7038" href="Level.html" class="Module">Level</a>

<a id="Lift-alg-op"></a><a id="7045" href="Base.Algebras.Basic.html#7045" class="Function">Lift-alg-op</a> <a id="7057" class="Symbol">:</a> <a id="7059" class="Symbol">{</a><a id="7060" href="Base.Algebras.Basic.html#7060" class="Bound">I</a> <a id="7062" class="Symbol">:</a> <a id="7064" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="7069" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a><a id="7070" class="Symbol">}</a> <a id="7072" class="Symbol">{</a><a id="7073" href="Base.Algebras.Basic.html#7073" class="Bound">A</a> <a id="7075" class="Symbol">:</a> <a id="7077" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="7082" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="7083" class="Symbol">}</a> <a id="7085" class="Symbol">→</a> <a id="7087" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="7090" href="Base.Algebras.Basic.html#7073" class="Bound">A</a> <a id="7092" href="Base.Algebras.Basic.html#7060" class="Bound">I</a> <a id="7094" class="Symbol">→</a> <a id="7096" class="Symbol">(</a><a id="7097" href="Base.Algebras.Basic.html#7097" class="Bound">β</a> <a id="7099" class="Symbol">:</a> <a id="7101" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="7106" class="Symbol">)</a> <a id="7108" class="Symbol">→</a> <a id="7110" href="Overture.Operations.html#1235" class="Function">Op</a> <a id="7113" class="Symbol">(</a><a id="7114" href="Level.html#400" class="Record">Lift</a> <a id="7119" href="Base.Algebras.Basic.html#7097" class="Bound">β</a> <a id="7121" href="Base.Algebras.Basic.html#7073" class="Bound">A</a><a id="7122" class="Symbol">)</a> <a id="7124" href="Base.Algebras.Basic.html#7060" class="Bound">I</a>
<a id="7126" href="Base.Algebras.Basic.html#7045" class="Function">Lift-alg-op</a> <a id="7138" href="Base.Algebras.Basic.html#7138" class="Bound">f</a> <a id="7140" href="Base.Algebras.Basic.html#7140" class="Bound">β</a> <a id="7142" class="Symbol">=</a> <a id="7144" class="Symbol">λ</a> <a id="7146" href="Base.Algebras.Basic.html#7146" class="Bound">x</a> <a id="7148" class="Symbol">→</a> <a id="7150" href="Level.html#457" class="InductiveConstructor">lift</a> <a id="7155" class="Symbol">(</a><a id="7156" href="Base.Algebras.Basic.html#7138" class="Bound">f</a> <a id="7158" class="Symbol">(λ</a> <a id="7161" href="Base.Algebras.Basic.html#7161" class="Bound">i</a> <a id="7163" class="Symbol">→</a> <a id="7165" href="Level.html#470" class="Field">lower</a> <a id="7171" class="Symbol">(</a><a id="7172" href="Base.Algebras.Basic.html#7146" class="Bound">x</a> <a id="7174" href="Base.Algebras.Basic.html#7161" class="Bound">i</a><a id="7175" class="Symbol">)))</a>

<a id="Lift-Alg"></a><a id="7180" href="Base.Algebras.Basic.html#7180" class="Function">Lift-Alg</a> <a id="7189" class="Symbol">:</a> <a id="7191" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="7199" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="7201" class="Symbol">→</a> <a id="7203" class="Symbol">(</a><a id="7204" href="Base.Algebras.Basic.html#7204" class="Bound">β</a> <a id="7206" class="Symbol">:</a> <a id="7208" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="7213" class="Symbol">)</a> <a id="7215" class="Symbol">→</a> <a id="7217" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="7225" class="Symbol">(</a><a id="7226" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="7228" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="7230" href="Base.Algebras.Basic.html#7204" class="Bound">β</a><a id="7231" class="Symbol">)</a>
<a id="7233" href="Base.Algebras.Basic.html#7180" class="Function">Lift-Alg</a> <a id="7242" href="Base.Algebras.Basic.html#7242" class="Bound">𝑨</a> <a id="7244" href="Base.Algebras.Basic.html#7244" class="Bound">β</a> <a id="7246" class="Symbol">=</a> <a id="7248" href="Level.html#400" class="Record">Lift</a> <a id="7253" href="Base.Algebras.Basic.html#7244" class="Bound">β</a> <a id="7255" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="7257" href="Base.Algebras.Basic.html#7242" class="Bound">𝑨</a> <a id="7259" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="7261" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="7263" class="Symbol">(λ</a> <a id="7266" class="Symbol">(</a><a id="7267" href="Base.Algebras.Basic.html#7267" class="Bound">𝑓</a> <a id="7269" class="Symbol">:</a> <a id="7271" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="7273" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="7275" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="7276" class="Symbol">)</a> <a id="7278" class="Symbol">→</a> <a id="7280" href="Base.Algebras.Basic.html#7045" class="Function">Lift-alg-op</a> <a id="7292" class="Symbol">(</a><a id="7293" href="Base.Algebras.Basic.html#7267" class="Bound">𝑓</a> <a id="7295" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="7297" href="Base.Algebras.Basic.html#7242" class="Bound">𝑨</a><a id="7298" class="Symbol">)</a> <a id="7300" href="Base.Algebras.Basic.html#7244" class="Bound">β</a><a id="7301" class="Symbol">)</a>

<a id="7304" class="Keyword">open</a> <a id="7309" href="Base.Algebras.Basic.html#4789" class="Module">algebra</a>

<a id="Lift-algebra"></a><a id="7318" href="Base.Algebras.Basic.html#7318" class="Function">Lift-algebra</a> <a id="7331" class="Symbol">:</a> <a id="7333" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="7341" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="7343" class="Symbol">→</a> <a id="7345" class="Symbol">(</a><a id="7346" href="Base.Algebras.Basic.html#7346" class="Bound">β</a> <a id="7348" class="Symbol">:</a> <a id="7350" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="7355" class="Symbol">)</a> <a id="7357" class="Symbol">→</a> <a id="7359" href="Base.Algebras.Basic.html#4789" class="Record">algebra</a> <a id="7367" class="Symbol">(</a><a id="7368" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="7370" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="7372" href="Base.Algebras.Basic.html#7346" class="Bound">β</a><a id="7373" class="Symbol">)</a>
<a id="7375" href="Base.Algebras.Basic.html#7318" class="Function">Lift-algebra</a>  <a id="7389" href="Base.Algebras.Basic.html#7389" class="Bound">𝑨</a> <a id="7391" href="Base.Algebras.Basic.html#7391" class="Bound">β</a> <a id="7393" class="Symbol">=</a>  <a id="7396" href="Base.Algebras.Basic.html#4851" class="InductiveConstructor">mkalg</a> <a id="7402" class="Symbol">(</a><a id="7403" href="Level.html#400" class="Record">Lift</a> <a id="7408" href="Base.Algebras.Basic.html#7391" class="Bound">β</a> <a id="7410" class="Symbol">(</a><a id="7411" href="Base.Algebras.Basic.html#4866" class="Field">carrier</a> <a id="7419" href="Base.Algebras.Basic.html#7389" class="Bound">𝑨</a><a id="7420" class="Symbol">))</a> <a id="7423" class="Symbol">(λ</a> <a id="7426" class="Symbol">(</a><a id="7427" href="Base.Algebras.Basic.html#7427" class="Bound">f</a> <a id="7429" class="Symbol">:</a> <a id="7431" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="7433" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="7435" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="7436" class="Symbol">)</a>
 <a id="7439" class="Symbol">→</a>                   <a id="7459" href="Base.Algebras.Basic.html#7045" class="Function">Lift-alg-op</a> <a id="7471" class="Symbol">((</a><a id="7473" href="Base.Algebras.Basic.html#4885" class="Field">opsymbol</a> <a id="7482" href="Base.Algebras.Basic.html#7389" class="Bound">𝑨</a><a id="7483" class="Symbol">)</a> <a id="7485" href="Base.Algebras.Basic.html#7427" class="Bound">f</a><a id="7486" class="Symbol">)</a> <a id="7488" href="Base.Algebras.Basic.html#7391" class="Bound">β</a><a id="7489" class="Symbol">)</a>

</pre>

What makes the `Lift-Alg` type so useful for resolving type level errors involving
algebras is the nice properties it possesses.  Indeed, the [agda-algebras][]
library contains formal proofs of the following facts.

+  [`Lift-Alg` is a homomorphism](Base.Homomorphisms.Basic.html#exmples-of-homomorphisms)
   (see [Base.Homomorphisms.Basic][])
+  [`Lift-Alg` is an algebraic invariant](Base.Homomorphisms.Isomorphisms.html#lift-is-an-algebraic-invariant")
   (see [Base.Homomorphisms.Isomorphisms][])
+  [`Lift-Alg` of a subalgebra is a subalgebra](Base.Subalgebras.Subalgebras.html#lifts-of-subalgebras)
   (see [Base.Subalgebras.Subalgebras][])
+  [`Lift-Alg` preserves identities](Base.Varieties.EquationalLogic.html#lift-invariance))
  (see [Base.Varieties.EquationalLogic][])


#### <a id="compatibility-of-binary-relations">Compatibility of binary relations</a>

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R`
a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is
*compatible* with all basic operations of `𝑨`. The formal definition is immediate
since all the work is done by the relation `|:`, which we defined above (see
[Base.Relations.Discrete][]).

<pre class="Agda">

<a id="compatible"></a><a id="8742" href="Base.Algebras.Basic.html#8742" class="Function">compatible</a> <a id="8753" class="Symbol">:</a> <a id="8755" class="Symbol">(</a><a id="8756" href="Base.Algebras.Basic.html#8756" class="Bound">𝑨</a> <a id="8758" class="Symbol">:</a> <a id="8760" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="8768" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="8769" class="Symbol">)</a> <a id="8771" class="Symbol">→</a> <a id="8773" href="Base.Algebras.Basic.html#812" class="Function">BinRel</a> <a id="8780" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="8782" href="Base.Algebras.Basic.html#8756" class="Bound">𝑨</a> <a id="8784" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="8786" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a> <a id="8788" class="Symbol">→</a> <a id="8790" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="8795" class="Symbol">(</a><a id="8796" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="8798" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8800" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="8802" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8804" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="8806" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8808" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a><a id="8809" class="Symbol">)</a>
<a id="8811" href="Base.Algebras.Basic.html#8742" class="Function">compatible</a>  <a id="8823" href="Base.Algebras.Basic.html#8823" class="Bound">𝑨</a> <a id="8825" href="Base.Algebras.Basic.html#8825" class="Bound">R</a> <a id="8827" class="Symbol">=</a> <a id="8829" class="Symbol">∀</a> <a id="8831" href="Base.Algebras.Basic.html#8831" class="Bound">𝑓</a> <a id="8833" class="Symbol">→</a> <a id="8835" class="Symbol">(</a><a id="8836" href="Base.Algebras.Basic.html#8831" class="Bound">𝑓</a> <a id="8838" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="8840" href="Base.Algebras.Basic.html#8823" class="Bound">𝑨</a><a id="8841" class="Symbol">)</a> <a id="8843" href="Base.Relations.Discrete.html#6787" class="Function Operator">|:</a> <a id="8846" href="Base.Algebras.Basic.html#8825" class="Bound">R</a>

<a id="compatible-pred"></a><a id="8849" href="Base.Algebras.Basic.html#8849" class="Function">compatible-pred</a> <a id="8865" class="Symbol">:</a> <a id="8867" class="Symbol">(</a><a id="8868" href="Base.Algebras.Basic.html#8868" class="Bound">𝑨</a> <a id="8870" class="Symbol">:</a> <a id="8872" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="8880" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="8881" class="Symbol">)</a> <a id="8883" class="Symbol">→</a> <a id="8885" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="8890" class="Symbol">(</a><a id="8891" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="8893" href="Base.Algebras.Basic.html#8868" class="Bound">𝑨</a> <a id="8895" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="8897" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="8899" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="8901" href="Base.Algebras.Basic.html#8868" class="Bound">𝑨</a> <a id="8903" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="8904" class="Symbol">)</a><a id="8905" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a> <a id="8907" class="Symbol">→</a> <a id="8909" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="8914" class="Symbol">(</a><a id="8915" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="8917" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8919" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="8921" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8923" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="8925" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="8927" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a><a id="8928" class="Symbol">)</a>
<a id="8930" href="Base.Algebras.Basic.html#8849" class="Function">compatible-pred</a>  <a id="8947" href="Base.Algebras.Basic.html#8947" class="Bound">𝑨</a> <a id="8949" href="Base.Algebras.Basic.html#8949" class="Bound">P</a> <a id="8951" class="Symbol">=</a> <a id="8953" class="Symbol">∀</a> <a id="8955" href="Base.Algebras.Basic.html#8955" class="Bound">𝑓</a> <a id="8957" class="Symbol">→</a> <a id="8959" class="Symbol">(</a><a id="8960" href="Base.Algebras.Basic.html#8955" class="Bound">𝑓</a> <a id="8962" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="8964" href="Base.Algebras.Basic.html#8947" class="Bound">𝑨</a><a id="8965" class="Symbol">)</a> <a id="8967" href="Base.Relations.Discrete.html#7103" class="Function Operator">|:pred</a> <a id="8974" href="Base.Algebras.Basic.html#8949" class="Bound">P</a>

</pre>

Recall, the `|:` type was defined in [Base.Relations.Discrete][] module.


#### <a id="compatibility-of-continuous-relations">Compatibility of continuous relations</a>

In the [Base.Relations.Continuous][] module, we defined a function called
`compatible-Rel` to represent the assertion that a given continuous relation is
compatible with a given operation. With that, it is easy to define a function,
which we call `compatible-Rel-alg`, representing compatibility of a continuous
relation with all operations of an algebra.  Similarly, we define the analogous
`compatible-REL-alg` function for the (even more general) type of *dependent
relations*.

<pre class="Agda">

<a id="9654" class="Keyword">module</a> <a id="9661" href="Base.Algebras.Basic.html#9661" class="Module">_</a> <a id="9663" class="Symbol">{</a><a id="9664" href="Base.Algebras.Basic.html#9664" class="Bound">I</a> <a id="9666" class="Symbol">:</a> <a id="9668" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="9673" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a><a id="9674" class="Symbol">}</a> <a id="9676" class="Keyword">where</a>

 <a id="9684" href="Base.Algebras.Basic.html#9684" class="Function">compatible-Rel-alg</a> <a id="9703" class="Symbol">:</a> <a id="9705" class="Symbol">(</a><a id="9706" href="Base.Algebras.Basic.html#9706" class="Bound">𝑨</a> <a id="9708" class="Symbol">:</a> <a id="9710" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="9718" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="9719" class="Symbol">)</a> <a id="9721" class="Symbol">→</a> <a id="9723" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="9727" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9729" href="Base.Algebras.Basic.html#9706" class="Bound">𝑨</a> <a id="9731" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9733" href="Base.Algebras.Basic.html#9664" class="Bound">I</a><a id="9734" class="Symbol">{</a><a id="9735" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a><a id="9736" class="Symbol">}</a> <a id="9738" class="Symbol">→</a> <a id="9740" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a><a id="9744" class="Symbol">(</a><a id="9745" href="Base.Algebras.Basic.html#453" class="Bound">𝓞</a> <a id="9747" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9749" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a> <a id="9751" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9753" href="Base.Algebras.Basic.html#455" class="Bound">𝓥</a> <a id="9755" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="9757" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a><a id="9758" class="Symbol">)</a>
 <a id="9761" href="Base.Algebras.Basic.html#9684" class="Function">compatible-Rel-alg</a> <a id="9780" href="Base.Algebras.Basic.html#9780" class="Bound">𝑨</a> <a id="9782" href="Base.Algebras.Basic.html#9782" class="Bound">R</a> <a id="9784" class="Symbol">=</a> <a id="9786" class="Symbol">∀</a> <a id="9788" class="Symbol">(</a><a id="9789" href="Base.Algebras.Basic.html#9789" class="Bound">𝑓</a> <a id="9791" class="Symbol">:</a> <a id="9793" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9795" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="9797" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9799" class="Symbol">)</a> <a id="9801" class="Symbol">→</a>  <a id="9804" href="Base.Relations.Continuous.html#5603" class="Function">compatible-Rel</a> <a id="9819" class="Symbol">(</a><a id="9820" href="Base.Algebras.Basic.html#9789" class="Bound">𝑓</a> <a id="9822" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="9824" href="Base.Algebras.Basic.html#9780" class="Bound">𝑨</a><a id="9825" class="Symbol">)</a> <a id="9827" href="Base.Algebras.Basic.html#9782" class="Bound">R</a>

 <a id="9831" href="Base.Algebras.Basic.html#9831" class="Function">compatible-REL-alg</a> <a id="9850" class="Symbol">:</a> <a id="9852" class="Symbol">(</a><a id="9853" href="Base.Algebras.Basic.html#9853" class="Bound">𝒜</a> <a id="9855" class="Symbol">:</a> <a id="9857" href="Base.Algebras.Basic.html#9664" class="Bound">I</a> <a id="9859" class="Symbol">→</a> <a id="9861" href="Base.Algebras.Basic.html#2774" class="Function">Algebra</a> <a id="9869" href="Base.Algebras.Basic.html#1163" class="Generalizable">α</a><a id="9870" class="Symbol">)</a> <a id="9872" class="Symbol">→</a> <a id="9874" href="Base.Relations.Continuous.html#4773" class="Function">REL</a> <a id="9878" href="Base.Algebras.Basic.html#9664" class="Bound">I</a> <a id="9880" class="Symbol">(λ</a> <a id="9883" href="Base.Algebras.Basic.html#9883" class="Bound">i</a> <a id="9885" class="Symbol">→</a> <a id="9887" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9889" href="Base.Algebras.Basic.html#9853" class="Bound">𝒜</a>  <a id="9892" href="Base.Algebras.Basic.html#9883" class="Bound">i</a> <a id="9894" href="Overture.Basic.html#4326" class="Function Operator">∣</a><a id="9895" class="Symbol">)</a> <a id="9897" class="Symbol">{</a><a id="9898" href="Base.Algebras.Basic.html#1167" class="Generalizable">ρ</a><a id="9899" class="Symbol">}</a> <a id="9901" class="Symbol">→</a> <a id="9903" href="Base.Algebras.Basic.html#603" class="Primitive">Type</a> <a id="9908" class="Symbol">_</a>
 <a id="9911" href="Base.Algebras.Basic.html#9831" class="Function">compatible-REL-alg</a> <a id="9930" href="Base.Algebras.Basic.html#9930" class="Bound">𝒜</a> <a id="9932" href="Base.Algebras.Basic.html#9932" class="Bound">R</a> <a id="9934" class="Symbol">=</a> <a id="9936" class="Symbol">∀</a> <a id="9938" class="Symbol">(</a> <a id="9940" href="Base.Algebras.Basic.html#9940" class="Bound">𝑓</a> <a id="9942" class="Symbol">:</a> <a id="9944" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9946" href="Base.Algebras.Basic.html#439" class="Bound">𝑆</a> <a id="9948" href="Overture.Basic.html#4326" class="Function Operator">∣</a> <a id="9950" class="Symbol">)</a> <a id="9952" class="Symbol">→</a>  <a id="9955" href="Base.Relations.Continuous.html#6317" class="Function">compatible-REL</a> <a id="9970" class="Symbol">(λ</a> <a id="9973" href="Base.Algebras.Basic.html#9973" class="Bound">i</a> <a id="9975" class="Symbol">→</a> <a id="9977" href="Base.Algebras.Basic.html#9940" class="Bound">𝑓</a> <a id="9979" href="Base.Algebras.Basic.html#5783" class="Function Operator">̂</a> <a id="9981" class="Symbol">(</a><a id="9982" href="Base.Algebras.Basic.html#9930" class="Bound">𝒜</a> <a id="9984" href="Base.Algebras.Basic.html#9973" class="Bound">i</a><a id="9985" class="Symbol">))</a> <a id="9988" href="Base.Algebras.Basic.html#9932" class="Bound">R</a>
</pre>

-------------------------------------

<span style="float:left;">[↑ Base.Algebras](Base.Algebras.html)</span>
<span style="float:right;">[Base.Algebras.Products →](Base.Algebras.Products.html)</span>

{% include UALib.Links.md %}
