---
layout: default
title : "Base.Complexity.CSP module (The Agda Universal Algebra Library)"
date : "2021-07-14"
author: "the agda-algebras development team"
---

### <a id="constraint-satisfaction-problems">Constraint Satisfaction Problems</a>

This is the [Base.Complexity.CSP][] module of the [Agda Universal Algebra Library][].

#### <a id="the-relational-formulation-of-csp">The relational formulation of CSP</a>

Let 𝒜 = (𝐴 , 𝑅ᵃ) be a *relational structure* (or 𝑅-structure), that is, a pair consisting
of a set 𝐴 along with a collection 𝑅ᵃ ⊆ ⋃ₙ 𝒫(𝐴ⁿ) of relations on 𝐴.

We associate with 𝒜 a *constraint satisfaction problem* denoted by CSP(𝒜), which is the
decision problem that is solved by finding an algorithm or program that does the following:

Take as input

+ an *instance*, which is an 𝑅-structure ℬ = (𝐵 , 𝑅ᵇ) (in the same signature as 𝒜)

Output

+ "yes" or "no" according as there is, or is not, a *solution*, which is a 𝑅-structure
  homomorphism h : ℬ → 𝒜.

If there is such an algorithm that takes at most a power of 𝑛 operations to process an
input structure ℬ of size 𝑛 (i.e., 𝑛 bits of memory are required to encode ℬ), then
we say that CSP(𝒜) is *tractable*.  Otherwise, CSP(𝒜) is *intractable*.

Equivalently, if we define

  CSP(𝒜) := \{ ℬ ∣ ℬ an 𝑅-structure and ∃ hom ℬ → 𝒜 \}

then the CSP problem described above is simply the membership problem for the subset
CSP(𝒜) of 𝑅 structures having homomorphisms into 𝒜.

That is, our algorithm must take as input an 𝑅-structure (a relational structure in the
signature of 𝒜) and decide whether or not it belongs to the set CSP(𝒜).



#### <a id="connection-to-algebraic-csp">Connection to algebraic CSP</a>

Let A be a set, let Op(A) denote the set of all operations, Rel(A) the set of all
relations, on A.

Given R ⊆ Rel(A), define the set of operations on A that preserve all relations
in R as follows:

∣: ⃖ R  =  \{ f ∈ Op(𝐴) ∣ ∀ r ∈ R, f ∣: r \}.

Recall, f ∣: r is our notation for `f Preserves r ⟶ r`, which means that r is a
subuniverse of a power of the algebra (A , {f}).

Equivalently, `f Preserves r ⟶ r means` the following: if f is 𝑚-ary and r is
𝑛-ary, then for every size-𝑚 collection 𝑎𝑠 of 𝑛-tuples from r (that is, ∣ 𝑎𝑠 ∣ = 𝑚
and ∀ a ∈ 𝑎𝑠, r a) we have r (f ∘ (zip 𝑎𝑠)).


If 𝒜 = (A , R) is a relational structure, then the set ∣: ⃖R of operations on A that
preserve all relations in R is called the set of *polymorphisms* of 𝒜.

Conversely, starting with a collection F ⊆ Op(A) of operations on A, define
the set of all relations preserved by the functions in F as follows:

F ⃗ ∣:  =  \{ r ∈ Rel(A) ∣ ∀ f ∈ F, f ∣: r \}.

It is easy to see that for all F ⊆ Op(A) and all R ⊆ Rel(A), we have

  F ⊆  ∣: ⃖ (F ⃗ ∣:)    and    R ⊆ (∣: ⃖ R) ⃗ ∣:.

Let 𝑨(R) denote the algebraic structure with domain A and operations ∣: ⃖ R.

Then every r ∈ R is a subalgebra of a power of 𝑨(R).

Clearly (∣: ⃖ R) ⃗ ∣: is the set 𝖲 (𝖯fin 𝑨(R)) of subalgebras of finite powers of 𝑨(R).

The reason this Galois connection is useful is due to the following fact (observed by
Peter Jeavons in the late 1990's):

*Theorem*. Let 𝒜 = (A, R) be a finite relational structure.
           If R' ⊆ (∣: ⃖ R) ⃗ ∣: is finite, then CSP((A, Γ'))
           is reducible in poly-time to CSP(𝒜)

In particular, the tractability of CSP(𝒜) depends only on its associated polymorphism
algebra, 𝑨(R) := (A , ∣: ⃖ R).

<pre class="Agda">

<a id="3385" class="Symbol">{-#</a> <a id="3389" class="Keyword">OPTIONS</a> <a id="3397" class="Pragma">--without-K</a> <a id="3409" class="Pragma">--exact-split</a> <a id="3423" class="Pragma">--safe</a> <a id="3430" class="Symbol">#-}</a>

<a id="3435" class="Keyword">open</a> <a id="3440" class="Keyword">import</a> <a id="3447" href="Overture.html" class="Module">Overture</a> <a id="3456" class="Keyword">using</a> <a id="3462" class="Symbol">(</a> <a id="3464" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="3466" class="Symbol">;</a> <a id="3468" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a> <a id="3470" class="Symbol">;</a> <a id="3472" href="Overture.Signatures.html#3303" class="Function">Signature</a> <a id="3482" class="Symbol">)</a>

<a id="3485" class="Keyword">module</a> <a id="3492" href="Base.Complexity.CSP.html" class="Module">Base.Complexity.CSP</a> <a id="3512" class="Symbol">{</a><a id="3513" href="Base.Complexity.CSP.html#3513" class="Bound">𝑆</a> <a id="3515" class="Symbol">:</a> <a id="3517" href="Overture.Signatures.html#3303" class="Function">Signature</a> <a id="3527" href="Overture.Signatures.html#648" class="Generalizable">𝓞</a> <a id="3529" href="Overture.Signatures.html#650" class="Generalizable">𝓥</a><a id="3530" class="Symbol">}</a> <a id="3532" class="Keyword">where</a>

<a id="3539" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3621" class="Keyword">open</a> <a id="3626" class="Keyword">import</a> <a id="3633" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3650" class="Keyword">using</a> <a id="3656" class="Symbol">(</a> <a id="3658" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3662" class="Symbol">;</a> <a id="3664" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3669" class="Symbol">;</a> <a id="3671" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3676" class="Symbol">)</a> <a id="3678" class="Keyword">renaming</a> <a id="3687" class="Symbol">(</a> <a id="3689" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3693" class="Symbol">to</a> <a id="3696" class="Primitive">Type</a> <a id="3701" class="Symbol">)</a>
<a id="3703" class="Keyword">open</a> <a id="3708" class="Keyword">import</a> <a id="3715" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3732" class="Keyword">using</a> <a id="3738" class="Symbol">(</a> <a id="3740" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3744" class="Symbol">)</a>
<a id="3746" class="Keyword">open</a> <a id="3751" class="Keyword">import</a> <a id="3758" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3775" class="Keyword">using</a> <a id="3781" class="Symbol">(</a> <a id="3783" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3790" class="Symbol">)</a>

<a id="3793" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3875" class="Keyword">open</a> <a id="3880" class="Keyword">import</a> <a id="3887" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>       <a id="3919" class="Keyword">using</a> <a id="3925" class="Symbol">(</a> <a id="3927" href="Base.Relations.Continuous.html#4769" class="Function">REL</a> <a id="3931" class="Symbol">;</a> <a id="3933" href="Base.Relations.Continuous.html#4878" class="Function">REL-syntax</a> <a id="3944" class="Symbol">)</a>
<a id="3946" class="Keyword">open</a> <a id="3951" class="Keyword">import</a> <a id="3958" href="Setoid.Algebras.Basic.html" class="Module">Setoid.Algebras.Basic</a>  <a id="3981" class="Symbol">{</a><a id="3982" class="Argument">𝑆</a> <a id="3984" class="Symbol">=</a> <a id="3986" href="Base.Complexity.CSP.html#3513" class="Bound">𝑆</a><a id="3987" class="Symbol">}</a>  <a id="3990" class="Keyword">using</a> <a id="3996" class="Symbol">(</a> <a id="3998" href="Setoid.Algebras.Basic.html#2837" class="Record">Algebra</a> <a id="4006" class="Symbol">)</a>

</pre>

#### <a id="constraints">Constraints</a>

A constraint c consists of

1. a scope function,  s : I → var, and

2. a constraint relation, i.e., a predicate over the function type I → D

        I ···> var
         .     .
          .   .
           ⌟ ⌞
            D

The *scope* of a constraint is an indexed subset of the set of variable symbols.
We could define a type for this, e.g.,

```
 Scope : Type ν → Type ι → _
 Scope V I = I → V
```

but we omit this definition because it's so simple; to reiterate,
a scope of "arity" I on "variables" V is simply a map from I to V,
where,

* I denotes the "number" of variables involved in the scope
* V denotes a collection (type) of "variable symbols"

<pre class="Agda">

<a id="4735" class="Keyword">module</a>  <a id="4743" href="Base.Complexity.CSP.html#4743" class="Module">_</a>              <a id="4758" class="Comment">-- levels for...</a>
        <a id="4783" class="Symbol">{</a><a id="4784" href="Base.Complexity.CSP.html#4784" class="Bound">ι</a> <a id="4786" class="Symbol">:</a> <a id="4788" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4793" class="Symbol">}</a>    <a id="4798" class="Comment">-- ...arity (or argument index) types</a>
        <a id="4844" class="Symbol">{</a><a id="4845" href="Base.Complexity.CSP.html#4845" class="Bound">ν</a> <a id="4847" class="Symbol">:</a> <a id="4849" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4854" class="Symbol">}</a>    <a id="4859" class="Comment">-- ...variable symbol types</a>
        <a id="4895" class="Symbol">{</a><a id="4896" href="Base.Complexity.CSP.html#4896" class="Bound">α</a> <a id="4898" href="Base.Complexity.CSP.html#4898" class="Bound">ℓ</a> <a id="4900" class="Symbol">:</a> <a id="4902" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4907" class="Symbol">}</a>  <a id="4910" class="Comment">-- ... domain types</a>
 <a id="4931" class="Keyword">where</a>
 <a id="4938" class="Keyword">open</a> <a id="4943" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4951" class="Keyword">record</a> <a id="4958" href="Base.Complexity.CSP.html#4958" class="Record">Constraint</a> <a id="4969" class="Symbol">(</a><a id="4970" href="Base.Complexity.CSP.html#4970" class="Bound">var</a> <a id="4974" class="Symbol">:</a> <a id="4976" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="4981" href="Base.Complexity.CSP.html#4845" class="Bound">ν</a><a id="4982" class="Symbol">)</a> <a id="4984" class="Symbol">(</a><a id="4985" href="Base.Complexity.CSP.html#4985" class="Bound">dom</a> <a id="4989" class="Symbol">:</a> <a id="4991" href="Base.Complexity.CSP.html#4970" class="Bound">var</a> <a id="4995" class="Symbol">→</a> <a id="4997" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="5004" href="Base.Complexity.CSP.html#4896" class="Bound">α</a> <a id="5006" href="Base.Complexity.CSP.html#4898" class="Bound">ℓ</a><a id="5007" class="Symbol">)</a> <a id="5009" class="Symbol">:</a> <a id="5011" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="5016" class="Symbol">(</a><a id="5017" href="Base.Complexity.CSP.html#4845" class="Bound">ν</a> <a id="5019" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5021" href="Base.Complexity.CSP.html#4896" class="Bound">α</a> <a id="5023" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5025" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="5030" href="Base.Complexity.CSP.html#4784" class="Bound">ι</a><a id="5031" class="Symbol">)</a> <a id="5033" class="Keyword">where</a>
  <a id="5041" class="Keyword">field</a>
   <a id="5050" href="Base.Complexity.CSP.html#5050" class="Field">arity</a>  <a id="5057" class="Symbol">:</a> <a id="5059" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="5064" href="Base.Complexity.CSP.html#4784" class="Bound">ι</a>               <a id="5080" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5140" href="Base.Complexity.CSP.html#5140" class="Field">scope</a>  <a id="5147" class="Symbol">:</a> <a id="5149" href="Base.Complexity.CSP.html#5050" class="Field">arity</a> <a id="5155" class="Symbol">→</a> <a id="5157" href="Base.Complexity.CSP.html#4970" class="Bound">var</a>          <a id="5170" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5224" href="Base.Complexity.CSP.html#5224" class="Field">rel</a>    <a id="5231" class="Symbol">:</a> <a id="5233" href="Base.Relations.Continuous.html#4878" class="Function">REL[</a> <a id="5238" href="Base.Complexity.CSP.html#5238" class="Bound">i</a> <a id="5240" href="Base.Relations.Continuous.html#4878" class="Function">∈</a> <a id="5242" href="Base.Complexity.CSP.html#5050" class="Field">arity</a> <a id="5248" href="Base.Relations.Continuous.html#4878" class="Function">]</a> <a id="5250" class="Symbol">(</a><a id="5251" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5259" class="Symbol">(</a><a id="5260" href="Base.Complexity.CSP.html#4985" class="Bound">dom</a> <a id="5264" class="Symbol">(</a><a id="5265" href="Base.Complexity.CSP.html#5140" class="Field">scope</a> <a id="5271" href="Base.Complexity.CSP.html#5238" class="Bound">i</a><a id="5272" class="Symbol">)))</a>   <a id="5278" class="Comment">-- The constraint relation.</a>

  <a id="5309" href="Base.Complexity.CSP.html#5309" class="Function">satisfies</a> <a id="5319" class="Symbol">:</a> <a id="5321" class="Symbol">(∀</a> <a id="5324" href="Base.Complexity.CSP.html#5324" class="Bound">v</a> <a id="5326" class="Symbol">→</a> <a id="5328" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5336" class="Symbol">(</a><a id="5337" href="Base.Complexity.CSP.html#4985" class="Bound">dom</a> <a id="5341" href="Base.Complexity.CSP.html#5324" class="Bound">v</a><a id="5342" class="Symbol">))</a> <a id="5345" class="Symbol">→</a> <a id="5347" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a>  <a id="5353" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5409" href="Base.Complexity.CSP.html#5309" class="Function">satisfies</a> <a id="5419" href="Base.Complexity.CSP.html#5419" class="Bound">f</a> <a id="5421" class="Symbol">=</a> <a id="5423" href="Base.Complexity.CSP.html#5224" class="Field">rel</a> <a id="5427" class="Symbol">(</a><a id="5428" href="Base.Complexity.CSP.html#5419" class="Bound">f</a> <a id="5430" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5432" href="Base.Complexity.CSP.html#5140" class="Field">scope</a><a id="5437" class="Symbol">)</a>      <a id="5444" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5531" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
</pre>


#### <a id="csp-templates-and-instances">CSP templates and instances</a>

A CSP "template" restricts the relations that may occur in instances of the problem.
A convenient way to specify a template is to give an indexed family
𝒜 : var → Algebra α ρ of algebras (one for each variable symbol in var)
and require that relations be subalgebras of the product ⨅ var 𝒜.

To construct a CSP instance, then, we just have to give a family 𝒜 of algebras, specify
the number (ar) of constraints, and for each i : ar, define a constraint as a relation
over (some of) the members of 𝒜.

An instance of a constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where

* 𝑉 denotes a set of "variables"
* 𝐷 denotes a "domain",
* 𝐶 denotes an indexed collection of constraints.

<pre class="Agda">

 <a id="6378" class="Keyword">open</a> <a id="6383" href="Setoid.Algebras.Basic.html#2837" class="Module">Algebra</a>
 <a id="6392" class="Keyword">open</a> <a id="6397" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6405" class="Keyword">record</a> <a id="6412" href="Base.Complexity.CSP.html#6412" class="Record">CSPInstance</a> <a id="6424" class="Symbol">(</a><a id="6425" href="Base.Complexity.CSP.html#6425" class="Bound">var</a> <a id="6429" class="Symbol">:</a> <a id="6431" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="6436" href="Base.Complexity.CSP.html#4845" class="Bound">ν</a><a id="6437" class="Symbol">)(</a><a id="6439" href="Base.Complexity.CSP.html#6439" class="Bound">𝒜</a> <a id="6441" class="Symbol">:</a> <a id="6443" href="Base.Complexity.CSP.html#6425" class="Bound">var</a> <a id="6447" class="Symbol">→</a> <a id="6449" href="Setoid.Algebras.Basic.html#2837" class="Record">Algebra</a> <a id="6457" href="Base.Complexity.CSP.html#4896" class="Bound">α</a> <a id="6459" href="Base.Complexity.CSP.html#4898" class="Bound">ℓ</a><a id="6460" class="Symbol">)</a> <a id="6462" class="Symbol">:</a> <a id="6464" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="6469" class="Symbol">(</a><a id="6470" href="Base.Complexity.CSP.html#4845" class="Bound">ν</a> <a id="6472" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6474" href="Base.Complexity.CSP.html#4896" class="Bound">α</a> <a id="6476" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6478" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6483" href="Base.Complexity.CSP.html#4784" class="Bound">ι</a><a id="6484" class="Symbol">)</a> <a id="6486" class="Keyword">where</a>
  <a id="6494" class="Keyword">field</a>
   <a id="6503" href="Base.Complexity.CSP.html#6503" class="Field">ar</a> <a id="6506" class="Symbol">:</a> <a id="6508" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="6513" href="Base.Complexity.CSP.html#4784" class="Bound">ι</a>       <a id="6521" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6569" href="Base.Complexity.CSP.html#6569" class="Field">cs</a> <a id="6572" class="Symbol">:</a> <a id="6574" class="Symbol">(</a><a id="6575" href="Base.Complexity.CSP.html#6575" class="Bound">i</a> <a id="6577" class="Symbol">:</a> <a id="6579" href="Base.Complexity.CSP.html#6503" class="Field">ar</a><a id="6581" class="Symbol">)</a> <a id="6583" class="Symbol">→</a> <a id="6585" href="Base.Complexity.CSP.html#4958" class="Record">Constraint</a> <a id="6596" href="Base.Complexity.CSP.html#6425" class="Bound">var</a> <a id="6600" class="Symbol">(λ</a> <a id="6603" href="Base.Complexity.CSP.html#6603" class="Bound">v</a> <a id="6605" class="Symbol">→</a> <a id="6607" href="Setoid.Algebras.Basic.html#2894" class="Field">Domain</a> <a id="6614" class="Symbol">(</a><a id="6615" href="Base.Complexity.CSP.html#6439" class="Bound">𝒜</a> <a id="6617" href="Base.Complexity.CSP.html#6603" class="Bound">v</a><a id="6618" class="Symbol">))</a>

  <a id="6624" href="Base.Complexity.CSP.html#6624" class="Function">isSolution</a> <a id="6635" class="Symbol">:</a> <a id="6637" class="Symbol">(∀</a> <a id="6640" href="Base.Complexity.CSP.html#6640" class="Bound">v</a> <a id="6642" class="Symbol">→</a> <a id="6644" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6652" class="Symbol">(</a><a id="6653" href="Setoid.Algebras.Basic.html#2894" class="Field">Domain</a> <a id="6660" class="Symbol">(</a><a id="6661" href="Base.Complexity.CSP.html#6439" class="Bound">𝒜</a> <a id="6663" href="Base.Complexity.CSP.html#6640" class="Bound">v</a><a id="6664" class="Symbol">)))</a> <a id="6668" class="Symbol">→</a> <a id="6670" href="Base.Complexity.CSP.html#3696" class="Primitive">Type</a> <a id="6675" class="Symbol">_</a>  <a id="6678" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6719" href="Base.Complexity.CSP.html#6624" class="Function">isSolution</a> <a id="6730" href="Base.Complexity.CSP.html#6730" class="Bound">f</a> <a id="6732" class="Symbol">=</a> <a id="6734" class="Symbol">∀</a> <a id="6736" href="Base.Complexity.CSP.html#6736" class="Bound">i</a> <a id="6738" class="Symbol">→</a> <a id="6740" class="Symbol">(</a><a id="6741" href="Base.Complexity.CSP.html#5309" class="Function">Constraint.satisfies</a> <a id="6762" class="Symbol">(</a><a id="6763" href="Base.Complexity.CSP.html#6569" class="Field">cs</a> <a id="6766" href="Base.Complexity.CSP.html#6736" class="Bound">i</a><a id="6767" class="Symbol">))</a> <a id="6770" href="Base.Complexity.CSP.html#6730" class="Bound">f</a>  <a id="6773" class="Comment">-- if it satisfies all the constraints.</a>

</pre>

--------------------------------

<span>[← Base.Complexity.Basic](Base.Complexity.Basic.html)</span>
<span style="float:right;">[Top ↑](index.html)</span>

{% include UALib.Links.md %}
