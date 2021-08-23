---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### <a id="constraint-satisfaction-problems">Constraint Satisfaction Problems</a>

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

<a id="3287" class="Symbol">{-#</a> <a id="3291" class="Keyword">OPTIONS</a> <a id="3299" class="Pragma">--without-K</a> <a id="3311" class="Pragma">--exact-split</a> <a id="3325" class="Pragma">--safe</a> <a id="3332" class="Symbol">#-}</a>

<a id="3337" class="Keyword">open</a> <a id="3342" class="Keyword">import</a> <a id="3349" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3364" class="Keyword">using</a> <a id="3370" class="Symbol">(</a> <a id="3372" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="3374" class="Symbol">;</a> <a id="3376" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a> <a id="3378" class="Symbol">;</a> <a id="3380" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="3390" class="Symbol">)</a>

<a id="3393" class="Keyword">module</a> <a id="3400" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3415" class="Symbol">{</a><a id="3416" href="Complexity.CSP.html#3416" class="Bound">𝑆</a> <a id="3418" class="Symbol">:</a> <a id="3420" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="3430" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="3432" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a><a id="3433" class="Symbol">}</a> <a id="3435" class="Keyword">where</a>

<a id="3442" class="Keyword">open</a> <a id="3447" class="Keyword">import</a> <a id="3454" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3471" class="Keyword">using</a> <a id="3477" class="Symbol">(</a> <a id="3479" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3483" class="Symbol">;</a> <a id="3485" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3490" class="Symbol">;</a> <a id="3492" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3497" class="Symbol">)</a> <a id="3499" class="Keyword">renaming</a> <a id="3508" class="Symbol">(</a> <a id="3510" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3514" class="Symbol">to</a> <a id="3517" class="Primitive">Type</a> <a id="3522" class="Symbol">)</a>
<a id="3524" class="Keyword">open</a> <a id="3529" class="Keyword">import</a> <a id="3536" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3553" class="Keyword">using</a> <a id="3559" class="Symbol">(</a> <a id="3561" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3565" class="Symbol">)</a>
<a id="3567" class="Keyword">open</a> <a id="3572" class="Keyword">import</a> <a id="3579" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3596" class="Keyword">using</a> <a id="3602" class="Symbol">(</a> <a id="3604" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3611" class="Symbol">)</a>


<a id="3615" class="Keyword">open</a> <a id="3620" class="Keyword">import</a> <a id="3627" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3651" class="Keyword">using</a> <a id="3657" class="Symbol">(</a> <a id="3659" href="Relations.Continuous.html#4190" class="Function">ΠΡ</a> <a id="3662" class="Symbol">;</a> <a id="3664" href="Relations.Continuous.html#4298" class="Function">ΠΡ-syntax</a> <a id="3674" class="Symbol">)</a>
<a id="3676" class="Keyword">open</a> <a id="3681" class="Keyword">import</a> <a id="3688" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3710" class="Symbol">{</a><a id="3711" class="Argument">𝑆</a> <a id="3713" class="Symbol">=</a> <a id="3715" href="Complexity.CSP.html#3416" class="Bound">𝑆</a><a id="3716" class="Symbol">}</a> <a id="3718" class="Keyword">using</a> <a id="3724" class="Symbol">(</a> <a id="3726" href="Algebras.Setoid.Basic.html#3113" class="Record">SetoidAlgebra</a> <a id="3740" class="Symbol">)</a>

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

<a id="4471" class="Keyword">module</a> <a id="4478" href="Complexity.CSP.html#4478" class="Module">_</a> <a id="4480" class="Comment">-- levels for...</a>
         <a id="4506" class="Symbol">{</a><a id="4507" href="Complexity.CSP.html#4507" class="Bound">ι</a> <a id="4509" class="Symbol">:</a> <a id="4511" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4516" class="Symbol">}</a> <a id="4518" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4565" class="Symbol">{</a><a id="4566" href="Complexity.CSP.html#4566" class="Bound">ν</a> <a id="4568" class="Symbol">:</a> <a id="4570" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4575" class="Symbol">}</a> <a id="4577" class="Comment">-- ...variable symbol types</a>
         <a id="4614" class="Symbol">{</a><a id="4615" href="Complexity.CSP.html#4615" class="Bound">α</a> <a id="4617" href="Complexity.CSP.html#4617" class="Bound">ℓ</a> <a id="4619" class="Symbol">:</a> <a id="4621" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4626" class="Symbol">}</a> <a id="4628" class="Comment">-- ... domain types</a>
         <a id="4657" class="Keyword">where</a>
 <a id="4664" class="Keyword">open</a> <a id="4669" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4677" class="Keyword">record</a> <a id="4684" href="Complexity.CSP.html#4684" class="Record">Constraint</a> <a id="4695" class="Symbol">(</a><a id="4696" href="Complexity.CSP.html#4696" class="Bound">var</a> <a id="4700" class="Symbol">:</a> <a id="4702" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="4707" href="Complexity.CSP.html#4566" class="Bound">ν</a><a id="4708" class="Symbol">)</a> <a id="4710" class="Symbol">(</a><a id="4711" href="Complexity.CSP.html#4711" class="Bound">dom</a> <a id="4715" class="Symbol">:</a> <a id="4717" href="Complexity.CSP.html#4696" class="Bound">var</a> <a id="4721" class="Symbol">→</a> <a id="4723" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4730" href="Complexity.CSP.html#4615" class="Bound">α</a> <a id="4732" href="Complexity.CSP.html#4617" class="Bound">ℓ</a><a id="4733" class="Symbol">)</a> <a id="4735" class="Symbol">:</a> <a id="4737" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="4742" class="Symbol">(</a><a id="4743" href="Complexity.CSP.html#4566" class="Bound">ν</a> <a id="4745" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4747" href="Complexity.CSP.html#4615" class="Bound">α</a> <a id="4749" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4751" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="4756" href="Complexity.CSP.html#4507" class="Bound">ι</a><a id="4757" class="Symbol">)</a> <a id="4759" class="Keyword">where</a>
  <a id="4767" class="Keyword">field</a>
   <a id="4776" href="Complexity.CSP.html#4776" class="Field">arity</a>  <a id="4783" class="Symbol">:</a> <a id="4785" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="4790" href="Complexity.CSP.html#4507" class="Bound">ι</a>               <a id="4806" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="4866" href="Complexity.CSP.html#4866" class="Field">scope</a>  <a id="4873" class="Symbol">:</a> <a id="4875" href="Complexity.CSP.html#4776" class="Field">arity</a> <a id="4881" class="Symbol">→</a> <a id="4883" href="Complexity.CSP.html#4696" class="Bound">var</a>          <a id="4896" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="4950" href="Complexity.CSP.html#4950" class="Field">rel</a>    <a id="4957" class="Symbol">:</a> <a id="4959" href="Relations.Continuous.html#4298" class="Function">ΠΡ[</a> <a id="4963" href="Complexity.CSP.html#4963" class="Bound">i</a> <a id="4965" href="Relations.Continuous.html#4298" class="Function">∈</a> <a id="4967" href="Complexity.CSP.html#4776" class="Field">arity</a> <a id="4973" href="Relations.Continuous.html#4298" class="Function">]</a> <a id="4975" class="Symbol">(</a><a id="4976" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="4984" class="Symbol">(</a><a id="4985" href="Complexity.CSP.html#4711" class="Bound">dom</a> <a id="4989" class="Symbol">(</a><a id="4990" href="Complexity.CSP.html#4866" class="Field">scope</a> <a id="4996" href="Complexity.CSP.html#4963" class="Bound">i</a><a id="4997" class="Symbol">)))</a>     <a id="5005" class="Comment">-- The constraint relation.</a>

  <a id="5036" href="Complexity.CSP.html#5036" class="Function">satisfies</a> <a id="5046" class="Symbol">:</a> <a id="5048" class="Symbol">(∀</a> <a id="5051" href="Complexity.CSP.html#5051" class="Bound">v</a> <a id="5053" class="Symbol">→</a> <a id="5055" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5063" class="Symbol">(</a><a id="5064" href="Complexity.CSP.html#4711" class="Bound">dom</a> <a id="5068" href="Complexity.CSP.html#5051" class="Bound">v</a><a id="5069" class="Symbol">))</a> <a id="5072" class="Symbol">→</a> <a id="5074" href="Complexity.CSP.html#3517" class="Primitive">Type</a>  <a id="5080" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5136" href="Complexity.CSP.html#5036" class="Function">satisfies</a> <a id="5146" href="Complexity.CSP.html#5146" class="Bound">f</a> <a id="5148" class="Symbol">=</a> <a id="5150" href="Complexity.CSP.html#4950" class="Field">rel</a> <a id="5154" class="Symbol">(</a><a id="5155" href="Complexity.CSP.html#5146" class="Bound">f</a> <a id="5157" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5159" href="Complexity.CSP.html#4866" class="Field">scope</a><a id="5164" class="Symbol">)</a>      <a id="5171" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5258" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
</pre>


#### <a id="csp-templates-and-instances">CSP templates and instances</a>

A CSP "template" restricts the relations that may occur in instances of the problem.
A convenient way to specify a template is to give an indexed family
𝒜 : var → SetoidAlgebra α ρ of algebras (one for each variable symbol in var)
and require that relations be subalgebras of the product ⨅ var 𝒜.

To construct a CSP instance, then, we just have to give a family 𝒜 of algebras, specify
the number (ar) of constraints, and for each i : ar, define a constraint as a relation
over (some of) the members of 𝒜.

An instance of a constraint satisfaction problem is a triple 𝑃 = (𝑉, 𝐷, 𝐶) where

* 𝑉 denotes a set of "variables"
* 𝐷 denotes a "domain",
* 𝐶 denotes an indexed collection of constraints.

<pre class="Agda">

 <a id="6111" class="Keyword">open</a> <a id="6116" href="Algebras.Setoid.Basic.html#3113" class="Module">SetoidAlgebra</a>
 <a id="6131" class="Keyword">open</a> <a id="6136" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6144" class="Keyword">record</a> <a id="6151" href="Complexity.CSP.html#6151" class="Record">CSPInstance</a> <a id="6163" class="Symbol">(</a><a id="6164" href="Complexity.CSP.html#6164" class="Bound">var</a> <a id="6168" class="Symbol">:</a> <a id="6170" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="6175" href="Complexity.CSP.html#4566" class="Bound">ν</a><a id="6176" class="Symbol">)(</a><a id="6178" href="Complexity.CSP.html#6178" class="Bound">𝒜</a> <a id="6180" class="Symbol">:</a> <a id="6182" href="Complexity.CSP.html#6164" class="Bound">var</a> <a id="6186" class="Symbol">→</a> <a id="6188" href="Algebras.Setoid.Basic.html#3113" class="Record">SetoidAlgebra</a> <a id="6202" href="Complexity.CSP.html#4615" class="Bound">α</a> <a id="6204" href="Complexity.CSP.html#4617" class="Bound">ℓ</a><a id="6205" class="Symbol">)</a> <a id="6207" class="Symbol">:</a> <a id="6209" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="6214" class="Symbol">(</a><a id="6215" href="Complexity.CSP.html#4566" class="Bound">ν</a> <a id="6217" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6219" href="Complexity.CSP.html#4615" class="Bound">α</a> <a id="6221" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6223" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6228" href="Complexity.CSP.html#4507" class="Bound">ι</a><a id="6229" class="Symbol">)</a> <a id="6231" class="Keyword">where</a>
  <a id="6239" class="Keyword">field</a>
   <a id="6248" href="Complexity.CSP.html#6248" class="Field">ar</a> <a id="6251" class="Symbol">:</a> <a id="6253" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="6258" href="Complexity.CSP.html#4507" class="Bound">ι</a>       <a id="6266" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6314" href="Complexity.CSP.html#6314" class="Field">cs</a> <a id="6317" class="Symbol">:</a> <a id="6319" class="Symbol">(</a><a id="6320" href="Complexity.CSP.html#6320" class="Bound">i</a> <a id="6322" class="Symbol">:</a> <a id="6324" href="Complexity.CSP.html#6248" class="Field">ar</a><a id="6326" class="Symbol">)</a> <a id="6328" class="Symbol">→</a> <a id="6330" href="Complexity.CSP.html#4684" class="Record">Constraint</a> <a id="6341" href="Complexity.CSP.html#6164" class="Bound">var</a> <a id="6345" class="Symbol">(λ</a> <a id="6348" href="Complexity.CSP.html#6348" class="Bound">v</a> <a id="6350" class="Symbol">→</a> <a id="6352" href="Algebras.Setoid.Basic.html#3179" class="Field">Domain</a> <a id="6359" class="Symbol">(</a><a id="6360" href="Complexity.CSP.html#6178" class="Bound">𝒜</a> <a id="6362" href="Complexity.CSP.html#6348" class="Bound">v</a><a id="6363" class="Symbol">))</a>

  <a id="6369" href="Complexity.CSP.html#6369" class="Function">isSolution</a> <a id="6380" class="Symbol">:</a> <a id="6382" class="Symbol">(∀</a> <a id="6385" href="Complexity.CSP.html#6385" class="Bound">v</a> <a id="6387" class="Symbol">→</a> <a id="6389" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6397" class="Symbol">(</a><a id="6398" href="Algebras.Setoid.Basic.html#3179" class="Field">Domain</a> <a id="6405" class="Symbol">(</a><a id="6406" href="Complexity.CSP.html#6178" class="Bound">𝒜</a> <a id="6408" href="Complexity.CSP.html#6385" class="Bound">v</a><a id="6409" class="Symbol">)))</a> <a id="6413" class="Symbol">→</a> <a id="6415" href="Complexity.CSP.html#3517" class="Primitive">Type</a> <a id="6420" class="Symbol">_</a>  <a id="6423" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6464" href="Complexity.CSP.html#6369" class="Function">isSolution</a> <a id="6475" href="Complexity.CSP.html#6475" class="Bound">f</a> <a id="6477" class="Symbol">=</a> <a id="6479" class="Symbol">∀</a> <a id="6481" href="Complexity.CSP.html#6481" class="Bound">i</a> <a id="6483" class="Symbol">→</a> <a id="6485" class="Symbol">(</a><a id="6486" href="Complexity.CSP.html#5036" class="Function">Constraint.satisfies</a> <a id="6507" class="Symbol">(</a><a id="6508" href="Complexity.CSP.html#6314" class="Field">cs</a> <a id="6511" href="Complexity.CSP.html#6481" class="Bound">i</a><a id="6512" class="Symbol">))</a> <a id="6515" href="Complexity.CSP.html#6475" class="Bound">f</a>  <a id="6518" class="Comment">-- if it satisfies all the constraints.</a>

</pre>


--------------------------------------

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


