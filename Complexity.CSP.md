---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

## <a id="constraint-satisfaction-problems">Constraint Satisfaction Problems</a>

This is the [Complexity.CSP][] module of the [Agda Universal Algebra Library][].

### <a id="the-relational-formulation-of-csp">The relational formulation of CSP</a>

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



### <a id="connection-to-algebraic-csp">Connection to algebraic CSP</a>

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

<a id="3366" class="Symbol">{-#</a> <a id="3370" class="Keyword">OPTIONS</a> <a id="3378" class="Pragma">--without-K</a> <a id="3390" class="Pragma">--exact-split</a> <a id="3404" class="Pragma">--safe</a> <a id="3411" class="Symbol">#-}</a>

<a id="3416" class="Keyword">open</a> <a id="3421" class="Keyword">import</a> <a id="3428" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3443" class="Keyword">using</a> <a id="3449" class="Symbol">(</a> <a id="3451" href="Algebras.Basic.html#1139" class="Generalizable">𝓞</a> <a id="3453" class="Symbol">;</a> <a id="3455" href="Algebras.Basic.html#1141" class="Generalizable">𝓥</a> <a id="3457" class="Symbol">;</a> <a id="3459" href="Algebras.Basic.html#3865" class="Function">Signature</a> <a id="3469" class="Symbol">)</a>

<a id="3472" class="Keyword">module</a> <a id="3479" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3494" class="Symbol">{</a><a id="3495" href="Complexity.CSP.html#3495" class="Bound">𝑆</a> <a id="3497" class="Symbol">:</a> <a id="3499" href="Algebras.Basic.html#3865" class="Function">Signature</a> <a id="3509" href="Algebras.Basic.html#1139" class="Generalizable">𝓞</a> <a id="3511" href="Algebras.Basic.html#1141" class="Generalizable">𝓥</a><a id="3512" class="Symbol">}</a> <a id="3514" class="Keyword">where</a>

<a id="3521" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3603" class="Keyword">open</a> <a id="3608" class="Keyword">import</a> <a id="3615" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3632" class="Keyword">using</a> <a id="3638" class="Symbol">(</a> <a id="3640" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3644" class="Symbol">;</a> <a id="3646" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3651" class="Symbol">;</a> <a id="3653" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3658" class="Symbol">)</a> <a id="3660" class="Keyword">renaming</a> <a id="3669" class="Symbol">(</a> <a id="3671" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3675" class="Symbol">to</a> <a id="3678" class="Primitive">Type</a> <a id="3683" class="Symbol">)</a>
<a id="3685" class="Keyword">open</a> <a id="3690" class="Keyword">import</a> <a id="3697" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3714" class="Keyword">using</a> <a id="3720" class="Symbol">(</a> <a id="3722" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3726" class="Symbol">)</a>
<a id="3728" class="Keyword">open</a> <a id="3733" class="Keyword">import</a> <a id="3740" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3757" class="Keyword">using</a> <a id="3763" class="Symbol">(</a> <a id="3765" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3772" class="Symbol">)</a>

<a id="3775" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3857" class="Keyword">open</a> <a id="3862" class="Keyword">import</a> <a id="3869" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3893" class="Keyword">using</a> <a id="3899" class="Symbol">(</a> <a id="3901" href="Relations.Continuous.html#4217" class="Function">ΠΡ</a> <a id="3904" class="Symbol">;</a> <a id="3906" href="Relations.Continuous.html#4325" class="Function">ΠΡ-syntax</a> <a id="3916" class="Symbol">)</a>
<a id="3918" class="Keyword">open</a> <a id="3923" class="Keyword">import</a> <a id="3930" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3952" class="Symbol">{</a><a id="3953" class="Argument">𝑆</a> <a id="3955" class="Symbol">=</a> <a id="3957" href="Complexity.CSP.html#3495" class="Bound">𝑆</a><a id="3958" class="Symbol">}</a> <a id="3960" class="Keyword">using</a> <a id="3966" class="Symbol">(</a> <a id="3968" href="Algebras.Setoid.Basic.html#3236" class="Record">SetoidAlgebra</a> <a id="3982" class="Symbol">)</a>

</pre>

### <a id="constraints">Constraints</a>

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

<a id="4710" class="Keyword">module</a> <a id="4717" href="Complexity.CSP.html#4717" class="Module">_</a> <a id="4719" class="Comment">-- levels for...</a>
         <a id="4745" class="Symbol">{</a><a id="4746" href="Complexity.CSP.html#4746" class="Bound">ι</a> <a id="4748" class="Symbol">:</a> <a id="4750" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4755" class="Symbol">}</a> <a id="4757" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4804" class="Symbol">{</a><a id="4805" href="Complexity.CSP.html#4805" class="Bound">ν</a> <a id="4807" class="Symbol">:</a> <a id="4809" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4814" class="Symbol">}</a> <a id="4816" class="Comment">-- ...variable symbol types</a>
         <a id="4853" class="Symbol">{</a><a id="4854" href="Complexity.CSP.html#4854" class="Bound">α</a> <a id="4856" href="Complexity.CSP.html#4856" class="Bound">ℓ</a> <a id="4858" class="Symbol">:</a> <a id="4860" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4865" class="Symbol">}</a> <a id="4867" class="Comment">-- ... domain types</a>
         <a id="4896" class="Keyword">where</a>
 <a id="4903" class="Keyword">open</a> <a id="4908" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4916" class="Keyword">record</a> <a id="4923" href="Complexity.CSP.html#4923" class="Record">Constraint</a> <a id="4934" class="Symbol">(</a><a id="4935" href="Complexity.CSP.html#4935" class="Bound">var</a> <a id="4939" class="Symbol">:</a> <a id="4941" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="4946" href="Complexity.CSP.html#4805" class="Bound">ν</a><a id="4947" class="Symbol">)</a> <a id="4949" class="Symbol">(</a><a id="4950" href="Complexity.CSP.html#4950" class="Bound">dom</a> <a id="4954" class="Symbol">:</a> <a id="4956" href="Complexity.CSP.html#4935" class="Bound">var</a> <a id="4960" class="Symbol">→</a> <a id="4962" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4969" href="Complexity.CSP.html#4854" class="Bound">α</a> <a id="4971" href="Complexity.CSP.html#4856" class="Bound">ℓ</a><a id="4972" class="Symbol">)</a> <a id="4974" class="Symbol">:</a> <a id="4976" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="4981" class="Symbol">(</a><a id="4982" href="Complexity.CSP.html#4805" class="Bound">ν</a> <a id="4984" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4986" href="Complexity.CSP.html#4854" class="Bound">α</a> <a id="4988" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4990" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="4995" href="Complexity.CSP.html#4746" class="Bound">ι</a><a id="4996" class="Symbol">)</a> <a id="4998" class="Keyword">where</a>
  <a id="5006" class="Keyword">field</a>
   <a id="5015" href="Complexity.CSP.html#5015" class="Field">arity</a>  <a id="5022" class="Symbol">:</a> <a id="5024" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="5029" href="Complexity.CSP.html#4746" class="Bound">ι</a>               <a id="5045" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5105" href="Complexity.CSP.html#5105" class="Field">scope</a>  <a id="5112" class="Symbol">:</a> <a id="5114" href="Complexity.CSP.html#5015" class="Field">arity</a> <a id="5120" class="Symbol">→</a> <a id="5122" href="Complexity.CSP.html#4935" class="Bound">var</a>          <a id="5135" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5189" href="Complexity.CSP.html#5189" class="Field">rel</a>    <a id="5196" class="Symbol">:</a> <a id="5198" href="Relations.Continuous.html#4325" class="Function">ΠΡ[</a> <a id="5202" href="Complexity.CSP.html#5202" class="Bound">i</a> <a id="5204" href="Relations.Continuous.html#4325" class="Function">∈</a> <a id="5206" href="Complexity.CSP.html#5015" class="Field">arity</a> <a id="5212" href="Relations.Continuous.html#4325" class="Function">]</a> <a id="5214" class="Symbol">(</a><a id="5215" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5223" class="Symbol">(</a><a id="5224" href="Complexity.CSP.html#4950" class="Bound">dom</a> <a id="5228" class="Symbol">(</a><a id="5229" href="Complexity.CSP.html#5105" class="Field">scope</a> <a id="5235" href="Complexity.CSP.html#5202" class="Bound">i</a><a id="5236" class="Symbol">)))</a>     <a id="5244" class="Comment">-- The constraint relation.</a>

  <a id="5275" href="Complexity.CSP.html#5275" class="Function">satisfies</a> <a id="5285" class="Symbol">:</a> <a id="5287" class="Symbol">(∀</a> <a id="5290" href="Complexity.CSP.html#5290" class="Bound">v</a> <a id="5292" class="Symbol">→</a> <a id="5294" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5302" class="Symbol">(</a><a id="5303" href="Complexity.CSP.html#4950" class="Bound">dom</a> <a id="5307" href="Complexity.CSP.html#5290" class="Bound">v</a><a id="5308" class="Symbol">))</a> <a id="5311" class="Symbol">→</a> <a id="5313" href="Complexity.CSP.html#3678" class="Primitive">Type</a>  <a id="5319" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5375" href="Complexity.CSP.html#5275" class="Function">satisfies</a> <a id="5385" href="Complexity.CSP.html#5385" class="Bound">f</a> <a id="5387" class="Symbol">=</a> <a id="5389" href="Complexity.CSP.html#5189" class="Field">rel</a> <a id="5393" class="Symbol">(</a><a id="5394" href="Complexity.CSP.html#5385" class="Bound">f</a> <a id="5396" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5398" href="Complexity.CSP.html#5105" class="Field">scope</a><a id="5403" class="Symbol">)</a>      <a id="5410" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5497" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
</pre>


### <a id="csp-templates-and-instances">CSP templates and instances</a>

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

 <a id="6349" class="Keyword">open</a> <a id="6354" href="Algebras.Setoid.Basic.html#3236" class="Module">SetoidAlgebra</a>
 <a id="6369" class="Keyword">open</a> <a id="6374" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6382" class="Keyword">record</a> <a id="6389" href="Complexity.CSP.html#6389" class="Record">CSPInstance</a> <a id="6401" class="Symbol">(</a><a id="6402" href="Complexity.CSP.html#6402" class="Bound">var</a> <a id="6406" class="Symbol">:</a> <a id="6408" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="6413" href="Complexity.CSP.html#4805" class="Bound">ν</a><a id="6414" class="Symbol">)(</a><a id="6416" href="Complexity.CSP.html#6416" class="Bound">𝒜</a> <a id="6418" class="Symbol">:</a> <a id="6420" href="Complexity.CSP.html#6402" class="Bound">var</a> <a id="6424" class="Symbol">→</a> <a id="6426" href="Algebras.Setoid.Basic.html#3236" class="Record">SetoidAlgebra</a> <a id="6440" href="Complexity.CSP.html#4854" class="Bound">α</a> <a id="6442" href="Complexity.CSP.html#4856" class="Bound">ℓ</a><a id="6443" class="Symbol">)</a> <a id="6445" class="Symbol">:</a> <a id="6447" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="6452" class="Symbol">(</a><a id="6453" href="Complexity.CSP.html#4805" class="Bound">ν</a> <a id="6455" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6457" href="Complexity.CSP.html#4854" class="Bound">α</a> <a id="6459" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6461" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6466" href="Complexity.CSP.html#4746" class="Bound">ι</a><a id="6467" class="Symbol">)</a> <a id="6469" class="Keyword">where</a>
  <a id="6477" class="Keyword">field</a>
   <a id="6486" href="Complexity.CSP.html#6486" class="Field">ar</a> <a id="6489" class="Symbol">:</a> <a id="6491" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="6496" href="Complexity.CSP.html#4746" class="Bound">ι</a>       <a id="6504" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6552" href="Complexity.CSP.html#6552" class="Field">cs</a> <a id="6555" class="Symbol">:</a> <a id="6557" class="Symbol">(</a><a id="6558" href="Complexity.CSP.html#6558" class="Bound">i</a> <a id="6560" class="Symbol">:</a> <a id="6562" href="Complexity.CSP.html#6486" class="Field">ar</a><a id="6564" class="Symbol">)</a> <a id="6566" class="Symbol">→</a> <a id="6568" href="Complexity.CSP.html#4923" class="Record">Constraint</a> <a id="6579" href="Complexity.CSP.html#6402" class="Bound">var</a> <a id="6583" class="Symbol">(λ</a> <a id="6586" href="Complexity.CSP.html#6586" class="Bound">v</a> <a id="6588" class="Symbol">→</a> <a id="6590" href="Algebras.Setoid.Basic.html#3299" class="Field">Domain</a> <a id="6597" class="Symbol">(</a><a id="6598" href="Complexity.CSP.html#6416" class="Bound">𝒜</a> <a id="6600" href="Complexity.CSP.html#6586" class="Bound">v</a><a id="6601" class="Symbol">))</a>

  <a id="6607" href="Complexity.CSP.html#6607" class="Function">isSolution</a> <a id="6618" class="Symbol">:</a> <a id="6620" class="Symbol">(∀</a> <a id="6623" href="Complexity.CSP.html#6623" class="Bound">v</a> <a id="6625" class="Symbol">→</a> <a id="6627" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6635" class="Symbol">(</a><a id="6636" href="Algebras.Setoid.Basic.html#3299" class="Field">Domain</a> <a id="6643" class="Symbol">(</a><a id="6644" href="Complexity.CSP.html#6416" class="Bound">𝒜</a> <a id="6646" href="Complexity.CSP.html#6623" class="Bound">v</a><a id="6647" class="Symbol">)))</a> <a id="6651" class="Symbol">→</a> <a id="6653" href="Complexity.CSP.html#3678" class="Primitive">Type</a> <a id="6658" class="Symbol">_</a>  <a id="6661" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6702" href="Complexity.CSP.html#6607" class="Function">isSolution</a> <a id="6713" href="Complexity.CSP.html#6713" class="Bound">f</a> <a id="6715" class="Symbol">=</a> <a id="6717" class="Symbol">∀</a> <a id="6719" href="Complexity.CSP.html#6719" class="Bound">i</a> <a id="6721" class="Symbol">→</a> <a id="6723" class="Symbol">(</a><a id="6724" href="Complexity.CSP.html#5275" class="Function">Constraint.satisfies</a> <a id="6745" class="Symbol">(</a><a id="6746" href="Complexity.CSP.html#6552" class="Field">cs</a> <a id="6749" href="Complexity.CSP.html#6719" class="Bound">i</a><a id="6750" class="Symbol">))</a> <a id="6753" href="Complexity.CSP.html#6713" class="Bound">f</a>  <a id="6756" class="Comment">-- if it satisfies all the constraints.</a>

</pre>


--------------------------------

<span>[← Complexity.Basic](Complexity.Basic.html)</span>
<span style="float:right;">[agda-algebras ↑](agda-algebras.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


