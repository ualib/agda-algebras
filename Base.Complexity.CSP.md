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

<a id="3435" class="Keyword">open</a> <a id="3440" class="Keyword">import</a> <a id="3447" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="3467" class="Keyword">using</a> <a id="3473" class="Symbol">(</a> <a id="3475" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓞</a> <a id="3477" class="Symbol">;</a> <a id="3479" href="Base.Algebras.Basic.html#1164" class="Generalizable">𝓥</a> <a id="3481" class="Symbol">;</a> <a id="3483" href="Base.Algebras.Basic.html#3890" class="Function">Signature</a> <a id="3493" class="Symbol">)</a>

<a id="3496" class="Keyword">module</a> <a id="3503" href="Base.Complexity.CSP.html" class="Module">Base.Complexity.CSP</a> <a id="3523" class="Symbol">{</a><a id="3524" href="Base.Complexity.CSP.html#3524" class="Bound">𝑆</a> <a id="3526" class="Symbol">:</a> <a id="3528" href="Base.Algebras.Basic.html#3890" class="Function">Signature</a> <a id="3538" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓞</a> <a id="3540" href="Base.Algebras.Basic.html#1164" class="Generalizable">𝓥</a><a id="3541" class="Symbol">}</a> <a id="3543" class="Keyword">where</a>

<a id="3550" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3632" class="Keyword">open</a> <a id="3637" class="Keyword">import</a> <a id="3644" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3661" class="Keyword">using</a> <a id="3667" class="Symbol">(</a> <a id="3669" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3673" class="Symbol">;</a> <a id="3675" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3680" class="Symbol">;</a> <a id="3682" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3687" class="Symbol">)</a> <a id="3689" class="Keyword">renaming</a> <a id="3698" class="Symbol">(</a> <a id="3700" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3704" class="Symbol">to</a> <a id="3707" class="Primitive">Type</a> <a id="3712" class="Symbol">)</a>
<a id="3714" class="Keyword">open</a> <a id="3719" class="Keyword">import</a> <a id="3726" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3743" class="Keyword">using</a> <a id="3749" class="Symbol">(</a> <a id="3751" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3755" class="Symbol">)</a>
<a id="3757" class="Keyword">open</a> <a id="3762" class="Keyword">import</a> <a id="3769" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3786" class="Keyword">using</a> <a id="3792" class="Symbol">(</a> <a id="3794" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3801" class="Symbol">)</a>

<a id="3804" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3886" class="Keyword">open</a> <a id="3891" class="Keyword">import</a> <a id="3898" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>       <a id="3930" class="Keyword">using</a> <a id="3936" class="Symbol">(</a> <a id="3938" href="Base.Relations.Continuous.html#4795" class="Function">REL</a> <a id="3942" class="Symbol">;</a> <a id="3944" href="Base.Relations.Continuous.html#4905" class="Function">REL-syntax</a> <a id="3955" class="Symbol">)</a>
<a id="3957" class="Keyword">open</a> <a id="3962" class="Keyword">import</a> <a id="3969" href="Setoid.Algebras.Basic.html" class="Module">Setoid.Algebras.Basic</a>  <a id="3992" class="Symbol">{</a><a id="3993" class="Argument">𝑆</a> <a id="3995" class="Symbol">=</a> <a id="3997" href="Base.Complexity.CSP.html#3524" class="Bound">𝑆</a><a id="3998" class="Symbol">}</a>  <a id="4001" class="Keyword">using</a> <a id="4007" class="Symbol">(</a> <a id="4009" href="Setoid.Algebras.Basic.html#2890" class="Record">Algebra</a> <a id="4017" class="Symbol">)</a>

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

<a id="4746" class="Keyword">module</a> <a id="4753" href="Base.Complexity.CSP.html#4753" class="Module">_</a>                <a id="4770" class="Comment">-- levels for...</a>
         <a id="4796" class="Symbol">{</a><a id="4797" href="Base.Complexity.CSP.html#4797" class="Bound">ι</a> <a id="4799" class="Symbol">:</a> <a id="4801" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4806" class="Symbol">}</a>    <a id="4811" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4858" class="Symbol">{</a><a id="4859" href="Base.Complexity.CSP.html#4859" class="Bound">ν</a> <a id="4861" class="Symbol">:</a> <a id="4863" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4868" class="Symbol">}</a>    <a id="4873" class="Comment">-- ...variable symbol types</a>
         <a id="4910" class="Symbol">{</a><a id="4911" href="Base.Complexity.CSP.html#4911" class="Bound">α</a> <a id="4913" href="Base.Complexity.CSP.html#4913" class="Bound">ℓ</a> <a id="4915" class="Symbol">:</a> <a id="4917" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4922" class="Symbol">}</a>  <a id="4925" class="Comment">-- ... domain types</a>
         <a id="4954" class="Keyword">where</a>
 <a id="4961" class="Keyword">open</a> <a id="4966" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4974" class="Keyword">record</a> <a id="4981" href="Base.Complexity.CSP.html#4981" class="Record">Constraint</a> <a id="4992" class="Symbol">(</a><a id="4993" href="Base.Complexity.CSP.html#4993" class="Bound">var</a> <a id="4997" class="Symbol">:</a> <a id="4999" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5004" href="Base.Complexity.CSP.html#4859" class="Bound">ν</a><a id="5005" class="Symbol">)</a> <a id="5007" class="Symbol">(</a><a id="5008" href="Base.Complexity.CSP.html#5008" class="Bound">dom</a> <a id="5012" class="Symbol">:</a> <a id="5014" href="Base.Complexity.CSP.html#4993" class="Bound">var</a> <a id="5018" class="Symbol">→</a> <a id="5020" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="5027" href="Base.Complexity.CSP.html#4911" class="Bound">α</a> <a id="5029" href="Base.Complexity.CSP.html#4913" class="Bound">ℓ</a><a id="5030" class="Symbol">)</a> <a id="5032" class="Symbol">:</a> <a id="5034" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5039" class="Symbol">(</a><a id="5040" href="Base.Complexity.CSP.html#4859" class="Bound">ν</a> <a id="5042" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5044" href="Base.Complexity.CSP.html#4911" class="Bound">α</a> <a id="5046" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5048" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="5053" href="Base.Complexity.CSP.html#4797" class="Bound">ι</a><a id="5054" class="Symbol">)</a> <a id="5056" class="Keyword">where</a>
  <a id="5064" class="Keyword">field</a>
   <a id="5073" href="Base.Complexity.CSP.html#5073" class="Field">arity</a>  <a id="5080" class="Symbol">:</a> <a id="5082" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5087" href="Base.Complexity.CSP.html#4797" class="Bound">ι</a>               <a id="5103" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5163" href="Base.Complexity.CSP.html#5163" class="Field">scope</a>  <a id="5170" class="Symbol">:</a> <a id="5172" href="Base.Complexity.CSP.html#5073" class="Field">arity</a> <a id="5178" class="Symbol">→</a> <a id="5180" href="Base.Complexity.CSP.html#4993" class="Bound">var</a>          <a id="5193" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5247" href="Base.Complexity.CSP.html#5247" class="Field">rel</a>    <a id="5254" class="Symbol">:</a> <a id="5256" href="Base.Relations.Continuous.html#4905" class="Function">REL[</a> <a id="5261" href="Base.Complexity.CSP.html#5261" class="Bound">i</a> <a id="5263" href="Base.Relations.Continuous.html#4905" class="Function">∈</a> <a id="5265" href="Base.Complexity.CSP.html#5073" class="Field">arity</a> <a id="5271" href="Base.Relations.Continuous.html#4905" class="Function">]</a> <a id="5273" class="Symbol">(</a><a id="5274" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5282" class="Symbol">(</a><a id="5283" href="Base.Complexity.CSP.html#5008" class="Bound">dom</a> <a id="5287" class="Symbol">(</a><a id="5288" href="Base.Complexity.CSP.html#5163" class="Field">scope</a> <a id="5294" href="Base.Complexity.CSP.html#5261" class="Bound">i</a><a id="5295" class="Symbol">)))</a>   <a id="5301" class="Comment">-- The constraint relation.</a>

  <a id="5332" href="Base.Complexity.CSP.html#5332" class="Function">satisfies</a> <a id="5342" class="Symbol">:</a> <a id="5344" class="Symbol">(∀</a> <a id="5347" href="Base.Complexity.CSP.html#5347" class="Bound">v</a> <a id="5349" class="Symbol">→</a> <a id="5351" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5359" class="Symbol">(</a><a id="5360" href="Base.Complexity.CSP.html#5008" class="Bound">dom</a> <a id="5364" href="Base.Complexity.CSP.html#5347" class="Bound">v</a><a id="5365" class="Symbol">))</a> <a id="5368" class="Symbol">→</a> <a id="5370" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a>  <a id="5376" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5432" href="Base.Complexity.CSP.html#5332" class="Function">satisfies</a> <a id="5442" href="Base.Complexity.CSP.html#5442" class="Bound">f</a> <a id="5444" class="Symbol">=</a> <a id="5446" href="Base.Complexity.CSP.html#5247" class="Field">rel</a> <a id="5450" class="Symbol">(</a><a id="5451" href="Base.Complexity.CSP.html#5442" class="Bound">f</a> <a id="5453" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5455" href="Base.Complexity.CSP.html#5163" class="Field">scope</a><a id="5460" class="Symbol">)</a>      <a id="5467" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5554" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6401" class="Keyword">open</a> <a id="6406" href="Setoid.Algebras.Basic.html#2890" class="Module">Algebra</a>
 <a id="6415" class="Keyword">open</a> <a id="6420" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6428" class="Keyword">record</a> <a id="6435" href="Base.Complexity.CSP.html#6435" class="Record">CSPInstance</a> <a id="6447" class="Symbol">(</a><a id="6448" href="Base.Complexity.CSP.html#6448" class="Bound">var</a> <a id="6452" class="Symbol">:</a> <a id="6454" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6459" href="Base.Complexity.CSP.html#4859" class="Bound">ν</a><a id="6460" class="Symbol">)(</a><a id="6462" href="Base.Complexity.CSP.html#6462" class="Bound">𝒜</a> <a id="6464" class="Symbol">:</a> <a id="6466" href="Base.Complexity.CSP.html#6448" class="Bound">var</a> <a id="6470" class="Symbol">→</a> <a id="6472" href="Setoid.Algebras.Basic.html#2890" class="Record">Algebra</a> <a id="6480" href="Base.Complexity.CSP.html#4911" class="Bound">α</a> <a id="6482" href="Base.Complexity.CSP.html#4913" class="Bound">ℓ</a><a id="6483" class="Symbol">)</a> <a id="6485" class="Symbol">:</a> <a id="6487" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6492" class="Symbol">(</a><a id="6493" href="Base.Complexity.CSP.html#4859" class="Bound">ν</a> <a id="6495" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6497" href="Base.Complexity.CSP.html#4911" class="Bound">α</a> <a id="6499" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6501" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6506" href="Base.Complexity.CSP.html#4797" class="Bound">ι</a><a id="6507" class="Symbol">)</a> <a id="6509" class="Keyword">where</a>
  <a id="6517" class="Keyword">field</a>
   <a id="6526" href="Base.Complexity.CSP.html#6526" class="Field">ar</a> <a id="6529" class="Symbol">:</a> <a id="6531" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6536" href="Base.Complexity.CSP.html#4797" class="Bound">ι</a>       <a id="6544" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6592" href="Base.Complexity.CSP.html#6592" class="Field">cs</a> <a id="6595" class="Symbol">:</a> <a id="6597" class="Symbol">(</a><a id="6598" href="Base.Complexity.CSP.html#6598" class="Bound">i</a> <a id="6600" class="Symbol">:</a> <a id="6602" href="Base.Complexity.CSP.html#6526" class="Field">ar</a><a id="6604" class="Symbol">)</a> <a id="6606" class="Symbol">→</a> <a id="6608" href="Base.Complexity.CSP.html#4981" class="Record">Constraint</a> <a id="6619" href="Base.Complexity.CSP.html#6448" class="Bound">var</a> <a id="6623" class="Symbol">(λ</a> <a id="6626" href="Base.Complexity.CSP.html#6626" class="Bound">v</a> <a id="6628" class="Symbol">→</a> <a id="6630" href="Setoid.Algebras.Basic.html#2947" class="Field">Domain</a> <a id="6637" class="Symbol">(</a><a id="6638" href="Base.Complexity.CSP.html#6462" class="Bound">𝒜</a> <a id="6640" href="Base.Complexity.CSP.html#6626" class="Bound">v</a><a id="6641" class="Symbol">))</a>

  <a id="6647" href="Base.Complexity.CSP.html#6647" class="Function">isSolution</a> <a id="6658" class="Symbol">:</a> <a id="6660" class="Symbol">(∀</a> <a id="6663" href="Base.Complexity.CSP.html#6663" class="Bound">v</a> <a id="6665" class="Symbol">→</a> <a id="6667" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6675" class="Symbol">(</a><a id="6676" href="Setoid.Algebras.Basic.html#2947" class="Field">Domain</a> <a id="6683" class="Symbol">(</a><a id="6684" href="Base.Complexity.CSP.html#6462" class="Bound">𝒜</a> <a id="6686" href="Base.Complexity.CSP.html#6663" class="Bound">v</a><a id="6687" class="Symbol">)))</a> <a id="6691" class="Symbol">→</a> <a id="6693" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6698" class="Symbol">_</a>  <a id="6701" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6742" href="Base.Complexity.CSP.html#6647" class="Function">isSolution</a> <a id="6753" href="Base.Complexity.CSP.html#6753" class="Bound">f</a> <a id="6755" class="Symbol">=</a> <a id="6757" class="Symbol">∀</a> <a id="6759" href="Base.Complexity.CSP.html#6759" class="Bound">i</a> <a id="6761" class="Symbol">→</a> <a id="6763" class="Symbol">(</a><a id="6764" href="Base.Complexity.CSP.html#5332" class="Function">Constraint.satisfies</a> <a id="6785" class="Symbol">(</a><a id="6786" href="Base.Complexity.CSP.html#6592" class="Field">cs</a> <a id="6789" href="Base.Complexity.CSP.html#6759" class="Bound">i</a><a id="6790" class="Symbol">))</a> <a id="6793" href="Base.Complexity.CSP.html#6753" class="Bound">f</a>  <a id="6796" class="Comment">-- if it satisfies all the constraints.</a>

</pre>

--------------------------------

<span>[← Base.Complexity.Basic](Base.Complexity.Basic.html)</span>
<span style="float:right;">[Top ↑](index.html)</span>

{% include UALib.Links.md %}
