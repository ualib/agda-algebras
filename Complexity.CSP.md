---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### <a id="constraint-satisfaction-problems">Constraint Satisfaction Problems</a>

This is the [Complexity.CSP][] module of the [Agda Universal Algebra Library][].

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

<a id="3369" class="Symbol">{-#</a> <a id="3373" class="Keyword">OPTIONS</a> <a id="3381" class="Pragma">--without-K</a> <a id="3393" class="Pragma">--exact-split</a> <a id="3407" class="Pragma">--safe</a> <a id="3414" class="Symbol">#-}</a>

<a id="3419" class="Keyword">open</a> <a id="3424" class="Keyword">import</a> <a id="3431" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3446" class="Keyword">using</a> <a id="3452" class="Symbol">(</a> <a id="3454" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="3456" class="Symbol">;</a> <a id="3458" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a> <a id="3460" class="Symbol">;</a> <a id="3462" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="3472" class="Symbol">)</a>

<a id="3475" class="Keyword">module</a> <a id="3482" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3497" class="Symbol">{</a><a id="3498" href="Complexity.CSP.html#3498" class="Bound">𝑆</a> <a id="3500" class="Symbol">:</a> <a id="3502" href="Algebras.Basic.html#3581" class="Function">Signature</a> <a id="3512" href="Algebras.Basic.html#1155" class="Generalizable">𝓞</a> <a id="3514" href="Algebras.Basic.html#1157" class="Generalizable">𝓥</a><a id="3515" class="Symbol">}</a> <a id="3517" class="Keyword">where</a>

<a id="3524" class="Keyword">open</a> <a id="3529" class="Keyword">import</a> <a id="3536" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3553" class="Keyword">using</a> <a id="3559" class="Symbol">(</a> <a id="3561" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3565" class="Symbol">;</a> <a id="3567" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3572" class="Symbol">;</a> <a id="3574" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3579" class="Symbol">)</a> <a id="3581" class="Keyword">renaming</a> <a id="3590" class="Symbol">(</a> <a id="3592" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3596" class="Symbol">to</a> <a id="3599" class="Primitive">Type</a> <a id="3604" class="Symbol">)</a>
<a id="3606" class="Keyword">open</a> <a id="3611" class="Keyword">import</a> <a id="3618" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3635" class="Keyword">using</a> <a id="3641" class="Symbol">(</a> <a id="3643" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3647" class="Symbol">)</a>
<a id="3649" class="Keyword">open</a> <a id="3654" class="Keyword">import</a> <a id="3661" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3678" class="Keyword">using</a> <a id="3684" class="Symbol">(</a> <a id="3686" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3693" class="Symbol">)</a>


<a id="3697" class="Keyword">open</a> <a id="3702" class="Keyword">import</a> <a id="3709" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3733" class="Keyword">using</a> <a id="3739" class="Symbol">(</a> <a id="3741" href="Relations.Continuous.html#4190" class="Function">ΠΡ</a> <a id="3744" class="Symbol">;</a> <a id="3746" href="Relations.Continuous.html#4298" class="Function">ΠΡ-syntax</a> <a id="3756" class="Symbol">)</a>
<a id="3758" class="Keyword">open</a> <a id="3763" class="Keyword">import</a> <a id="3770" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3792" class="Symbol">{</a><a id="3793" class="Argument">𝑆</a> <a id="3795" class="Symbol">=</a> <a id="3797" href="Complexity.CSP.html#3498" class="Bound">𝑆</a><a id="3798" class="Symbol">}</a> <a id="3800" class="Keyword">using</a> <a id="3806" class="Symbol">(</a> <a id="3808" href="Algebras.Setoid.Basic.html#3299" class="Record">SetoidAlgebra</a> <a id="3822" class="Symbol">)</a>

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

<a id="4553" class="Keyword">module</a> <a id="4560" href="Complexity.CSP.html#4560" class="Module">_</a> <a id="4562" class="Comment">-- levels for...</a>
         <a id="4588" class="Symbol">{</a><a id="4589" href="Complexity.CSP.html#4589" class="Bound">ι</a> <a id="4591" class="Symbol">:</a> <a id="4593" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4598" class="Symbol">}</a> <a id="4600" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4647" class="Symbol">{</a><a id="4648" href="Complexity.CSP.html#4648" class="Bound">ν</a> <a id="4650" class="Symbol">:</a> <a id="4652" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4657" class="Symbol">}</a> <a id="4659" class="Comment">-- ...variable symbol types</a>
         <a id="4696" class="Symbol">{</a><a id="4697" href="Complexity.CSP.html#4697" class="Bound">α</a> <a id="4699" href="Complexity.CSP.html#4699" class="Bound">ℓ</a> <a id="4701" class="Symbol">:</a> <a id="4703" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4708" class="Symbol">}</a> <a id="4710" class="Comment">-- ... domain types</a>
         <a id="4739" class="Keyword">where</a>
 <a id="4746" class="Keyword">open</a> <a id="4751" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4759" class="Keyword">record</a> <a id="4766" href="Complexity.CSP.html#4766" class="Record">Constraint</a> <a id="4777" class="Symbol">(</a><a id="4778" href="Complexity.CSP.html#4778" class="Bound">var</a> <a id="4782" class="Symbol">:</a> <a id="4784" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="4789" href="Complexity.CSP.html#4648" class="Bound">ν</a><a id="4790" class="Symbol">)</a> <a id="4792" class="Symbol">(</a><a id="4793" href="Complexity.CSP.html#4793" class="Bound">dom</a> <a id="4797" class="Symbol">:</a> <a id="4799" href="Complexity.CSP.html#4778" class="Bound">var</a> <a id="4803" class="Symbol">→</a> <a id="4805" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4812" href="Complexity.CSP.html#4697" class="Bound">α</a> <a id="4814" href="Complexity.CSP.html#4699" class="Bound">ℓ</a><a id="4815" class="Symbol">)</a> <a id="4817" class="Symbol">:</a> <a id="4819" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="4824" class="Symbol">(</a><a id="4825" href="Complexity.CSP.html#4648" class="Bound">ν</a> <a id="4827" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4829" href="Complexity.CSP.html#4697" class="Bound">α</a> <a id="4831" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4833" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="4838" href="Complexity.CSP.html#4589" class="Bound">ι</a><a id="4839" class="Symbol">)</a> <a id="4841" class="Keyword">where</a>
  <a id="4849" class="Keyword">field</a>
   <a id="4858" href="Complexity.CSP.html#4858" class="Field">arity</a>  <a id="4865" class="Symbol">:</a> <a id="4867" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="4872" href="Complexity.CSP.html#4589" class="Bound">ι</a>               <a id="4888" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="4948" href="Complexity.CSP.html#4948" class="Field">scope</a>  <a id="4955" class="Symbol">:</a> <a id="4957" href="Complexity.CSP.html#4858" class="Field">arity</a> <a id="4963" class="Symbol">→</a> <a id="4965" href="Complexity.CSP.html#4778" class="Bound">var</a>          <a id="4978" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5032" href="Complexity.CSP.html#5032" class="Field">rel</a>    <a id="5039" class="Symbol">:</a> <a id="5041" href="Relations.Continuous.html#4298" class="Function">ΠΡ[</a> <a id="5045" href="Complexity.CSP.html#5045" class="Bound">i</a> <a id="5047" href="Relations.Continuous.html#4298" class="Function">∈</a> <a id="5049" href="Complexity.CSP.html#4858" class="Field">arity</a> <a id="5055" href="Relations.Continuous.html#4298" class="Function">]</a> <a id="5057" class="Symbol">(</a><a id="5058" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5066" class="Symbol">(</a><a id="5067" href="Complexity.CSP.html#4793" class="Bound">dom</a> <a id="5071" class="Symbol">(</a><a id="5072" href="Complexity.CSP.html#4948" class="Field">scope</a> <a id="5078" href="Complexity.CSP.html#5045" class="Bound">i</a><a id="5079" class="Symbol">)))</a>     <a id="5087" class="Comment">-- The constraint relation.</a>

  <a id="5118" href="Complexity.CSP.html#5118" class="Function">satisfies</a> <a id="5128" class="Symbol">:</a> <a id="5130" class="Symbol">(∀</a> <a id="5133" href="Complexity.CSP.html#5133" class="Bound">v</a> <a id="5135" class="Symbol">→</a> <a id="5137" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5145" class="Symbol">(</a><a id="5146" href="Complexity.CSP.html#4793" class="Bound">dom</a> <a id="5150" href="Complexity.CSP.html#5133" class="Bound">v</a><a id="5151" class="Symbol">))</a> <a id="5154" class="Symbol">→</a> <a id="5156" href="Complexity.CSP.html#3599" class="Primitive">Type</a>  <a id="5162" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5218" href="Complexity.CSP.html#5118" class="Function">satisfies</a> <a id="5228" href="Complexity.CSP.html#5228" class="Bound">f</a> <a id="5230" class="Symbol">=</a> <a id="5232" href="Complexity.CSP.html#5032" class="Field">rel</a> <a id="5236" class="Symbol">(</a><a id="5237" href="Complexity.CSP.html#5228" class="Bound">f</a> <a id="5239" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5241" href="Complexity.CSP.html#4948" class="Field">scope</a><a id="5246" class="Symbol">)</a>      <a id="5253" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5340" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6193" class="Keyword">open</a> <a id="6198" href="Algebras.Setoid.Basic.html#3299" class="Module">SetoidAlgebra</a>
 <a id="6213" class="Keyword">open</a> <a id="6218" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6226" class="Keyword">record</a> <a id="6233" href="Complexity.CSP.html#6233" class="Record">CSPInstance</a> <a id="6245" class="Symbol">(</a><a id="6246" href="Complexity.CSP.html#6246" class="Bound">var</a> <a id="6250" class="Symbol">:</a> <a id="6252" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="6257" href="Complexity.CSP.html#4648" class="Bound">ν</a><a id="6258" class="Symbol">)(</a><a id="6260" href="Complexity.CSP.html#6260" class="Bound">𝒜</a> <a id="6262" class="Symbol">:</a> <a id="6264" href="Complexity.CSP.html#6246" class="Bound">var</a> <a id="6268" class="Symbol">→</a> <a id="6270" href="Algebras.Setoid.Basic.html#3299" class="Record">SetoidAlgebra</a> <a id="6284" href="Complexity.CSP.html#4697" class="Bound">α</a> <a id="6286" href="Complexity.CSP.html#4699" class="Bound">ℓ</a><a id="6287" class="Symbol">)</a> <a id="6289" class="Symbol">:</a> <a id="6291" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="6296" class="Symbol">(</a><a id="6297" href="Complexity.CSP.html#4648" class="Bound">ν</a> <a id="6299" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6301" href="Complexity.CSP.html#4697" class="Bound">α</a> <a id="6303" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6305" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6310" href="Complexity.CSP.html#4589" class="Bound">ι</a><a id="6311" class="Symbol">)</a> <a id="6313" class="Keyword">where</a>
  <a id="6321" class="Keyword">field</a>
   <a id="6330" href="Complexity.CSP.html#6330" class="Field">ar</a> <a id="6333" class="Symbol">:</a> <a id="6335" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="6340" href="Complexity.CSP.html#4589" class="Bound">ι</a>       <a id="6348" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6396" href="Complexity.CSP.html#6396" class="Field">cs</a> <a id="6399" class="Symbol">:</a> <a id="6401" class="Symbol">(</a><a id="6402" href="Complexity.CSP.html#6402" class="Bound">i</a> <a id="6404" class="Symbol">:</a> <a id="6406" href="Complexity.CSP.html#6330" class="Field">ar</a><a id="6408" class="Symbol">)</a> <a id="6410" class="Symbol">→</a> <a id="6412" href="Complexity.CSP.html#4766" class="Record">Constraint</a> <a id="6423" href="Complexity.CSP.html#6246" class="Bound">var</a> <a id="6427" class="Symbol">(λ</a> <a id="6430" href="Complexity.CSP.html#6430" class="Bound">v</a> <a id="6432" class="Symbol">→</a> <a id="6434" href="Algebras.Setoid.Basic.html#3365" class="Field">Domain</a> <a id="6441" class="Symbol">(</a><a id="6442" href="Complexity.CSP.html#6260" class="Bound">𝒜</a> <a id="6444" href="Complexity.CSP.html#6430" class="Bound">v</a><a id="6445" class="Symbol">))</a>

  <a id="6451" href="Complexity.CSP.html#6451" class="Function">isSolution</a> <a id="6462" class="Symbol">:</a> <a id="6464" class="Symbol">(∀</a> <a id="6467" href="Complexity.CSP.html#6467" class="Bound">v</a> <a id="6469" class="Symbol">→</a> <a id="6471" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6479" class="Symbol">(</a><a id="6480" href="Algebras.Setoid.Basic.html#3365" class="Field">Domain</a> <a id="6487" class="Symbol">(</a><a id="6488" href="Complexity.CSP.html#6260" class="Bound">𝒜</a> <a id="6490" href="Complexity.CSP.html#6467" class="Bound">v</a><a id="6491" class="Symbol">)))</a> <a id="6495" class="Symbol">→</a> <a id="6497" href="Complexity.CSP.html#3599" class="Primitive">Type</a> <a id="6502" class="Symbol">_</a>  <a id="6505" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6546" href="Complexity.CSP.html#6451" class="Function">isSolution</a> <a id="6557" href="Complexity.CSP.html#6557" class="Bound">f</a> <a id="6559" class="Symbol">=</a> <a id="6561" class="Symbol">∀</a> <a id="6563" href="Complexity.CSP.html#6563" class="Bound">i</a> <a id="6565" class="Symbol">→</a> <a id="6567" class="Symbol">(</a><a id="6568" href="Complexity.CSP.html#5118" class="Function">Constraint.satisfies</a> <a id="6589" class="Symbol">(</a><a id="6590" href="Complexity.CSP.html#6396" class="Field">cs</a> <a id="6593" href="Complexity.CSP.html#6563" class="Bound">i</a><a id="6594" class="Symbol">))</a> <a id="6597" href="Complexity.CSP.html#6557" class="Bound">f</a>  <a id="6600" class="Comment">-- if it satisfies all the constraints.</a>

</pre>


--------------------------------

<br>

[← Complexity.Basic](Complexity.Basic.html)
<span style="float:right;">[agda-algebras ↑](agda-algebras.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


