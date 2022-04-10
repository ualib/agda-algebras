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

<a id="3435" class="Keyword">open</a> <a id="3440" class="Keyword">import</a> <a id="3447" href="Base.Algebras.Basic.html" class="Module">Base.Algebras.Basic</a> <a id="3467" class="Keyword">using</a> <a id="3473" class="Symbol">(</a> <a id="3475" href="Base.Algebras.Basic.html#1160" class="Generalizable">𝓞</a> <a id="3477" class="Symbol">;</a> <a id="3479" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓥</a> <a id="3481" class="Symbol">;</a> <a id="3483" href="Base.Algebras.Basic.html#3888" class="Function">Signature</a> <a id="3493" class="Symbol">)</a>

<a id="3496" class="Keyword">module</a> <a id="3503" href="Base.Complexity.CSP.html" class="Module">Base.Complexity.CSP</a> <a id="3523" class="Symbol">{</a><a id="3524" href="Base.Complexity.CSP.html#3524" class="Bound">𝑆</a> <a id="3526" class="Symbol">:</a> <a id="3528" href="Base.Algebras.Basic.html#3888" class="Function">Signature</a> <a id="3538" href="Base.Algebras.Basic.html#1160" class="Generalizable">𝓞</a> <a id="3540" href="Base.Algebras.Basic.html#1162" class="Generalizable">𝓥</a><a id="3541" class="Symbol">}</a> <a id="3543" class="Keyword">where</a>

<a id="3550" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3632" class="Keyword">open</a> <a id="3637" class="Keyword">import</a> <a id="3644" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3661" class="Keyword">using</a> <a id="3667" class="Symbol">(</a> <a id="3669" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3673" class="Symbol">;</a> <a id="3675" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3680" class="Symbol">;</a> <a id="3682" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3687" class="Symbol">)</a> <a id="3689" class="Keyword">renaming</a> <a id="3698" class="Symbol">(</a> <a id="3700" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3704" class="Symbol">to</a> <a id="3707" class="Primitive">Type</a> <a id="3712" class="Symbol">)</a>
<a id="3714" class="Keyword">open</a> <a id="3719" class="Keyword">import</a> <a id="3726" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3743" class="Keyword">using</a> <a id="3749" class="Symbol">(</a> <a id="3751" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3755" class="Symbol">)</a>
<a id="3757" class="Keyword">open</a> <a id="3762" class="Keyword">import</a> <a id="3769" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3786" class="Keyword">using</a> <a id="3792" class="Symbol">(</a> <a id="3794" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3801" class="Symbol">)</a>

<a id="3804" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3886" class="Keyword">open</a> <a id="3891" class="Keyword">import</a> <a id="3898" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>       <a id="3930" class="Keyword">using</a> <a id="3936" class="Symbol">(</a> <a id="3938" href="Base.Relations.Continuous.html#4256" class="Function">ΠΡ</a> <a id="3941" class="Symbol">;</a> <a id="3943" href="Base.Relations.Continuous.html#4364" class="Function">ΠΡ-syntax</a> <a id="3953" class="Symbol">)</a>
<a id="3955" class="Keyword">open</a> <a id="3960" class="Keyword">import</a> <a id="3967" href="Setoid.Algebras.Basic.html" class="Module">Setoid.Algebras.Basic</a>  <a id="3990" class="Symbol">{</a><a id="3991" class="Argument">𝑆</a> <a id="3993" class="Symbol">=</a> <a id="3995" href="Base.Complexity.CSP.html#3524" class="Bound">𝑆</a><a id="3996" class="Symbol">}</a>  <a id="3999" class="Keyword">using</a> <a id="4005" class="Symbol">(</a> <a id="4007" href="Setoid.Algebras.Basic.html#2890" class="Record">Algebra</a> <a id="4015" class="Symbol">)</a>

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

<a id="4744" class="Keyword">module</a> <a id="4751" href="Base.Complexity.CSP.html#4751" class="Module">_</a>                <a id="4768" class="Comment">-- levels for...</a>
         <a id="4794" class="Symbol">{</a><a id="4795" href="Base.Complexity.CSP.html#4795" class="Bound">ι</a> <a id="4797" class="Symbol">:</a> <a id="4799" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4804" class="Symbol">}</a>    <a id="4809" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4856" class="Symbol">{</a><a id="4857" href="Base.Complexity.CSP.html#4857" class="Bound">ν</a> <a id="4859" class="Symbol">:</a> <a id="4861" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4866" class="Symbol">}</a>    <a id="4871" class="Comment">-- ...variable symbol types</a>
         <a id="4908" class="Symbol">{</a><a id="4909" href="Base.Complexity.CSP.html#4909" class="Bound">α</a> <a id="4911" href="Base.Complexity.CSP.html#4911" class="Bound">ℓ</a> <a id="4913" class="Symbol">:</a> <a id="4915" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4920" class="Symbol">}</a>  <a id="4923" class="Comment">-- ... domain types</a>
         <a id="4952" class="Keyword">where</a>
 <a id="4959" class="Keyword">open</a> <a id="4964" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4972" class="Keyword">record</a> <a id="4979" href="Base.Complexity.CSP.html#4979" class="Record">Constraint</a> <a id="4990" class="Symbol">(</a><a id="4991" href="Base.Complexity.CSP.html#4991" class="Bound">var</a> <a id="4995" class="Symbol">:</a> <a id="4997" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5002" href="Base.Complexity.CSP.html#4857" class="Bound">ν</a><a id="5003" class="Symbol">)</a> <a id="5005" class="Symbol">(</a><a id="5006" href="Base.Complexity.CSP.html#5006" class="Bound">dom</a> <a id="5010" class="Symbol">:</a> <a id="5012" href="Base.Complexity.CSP.html#4991" class="Bound">var</a> <a id="5016" class="Symbol">→</a> <a id="5018" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="5025" href="Base.Complexity.CSP.html#4909" class="Bound">α</a> <a id="5027" href="Base.Complexity.CSP.html#4911" class="Bound">ℓ</a><a id="5028" class="Symbol">)</a> <a id="5030" class="Symbol">:</a> <a id="5032" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5037" class="Symbol">(</a><a id="5038" href="Base.Complexity.CSP.html#4857" class="Bound">ν</a> <a id="5040" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5042" href="Base.Complexity.CSP.html#4909" class="Bound">α</a> <a id="5044" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5046" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="5051" href="Base.Complexity.CSP.html#4795" class="Bound">ι</a><a id="5052" class="Symbol">)</a> <a id="5054" class="Keyword">where</a>
  <a id="5062" class="Keyword">field</a>
   <a id="5071" href="Base.Complexity.CSP.html#5071" class="Field">arity</a>  <a id="5078" class="Symbol">:</a> <a id="5080" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="5085" href="Base.Complexity.CSP.html#4795" class="Bound">ι</a>               <a id="5101" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5161" href="Base.Complexity.CSP.html#5161" class="Field">scope</a>  <a id="5168" class="Symbol">:</a> <a id="5170" href="Base.Complexity.CSP.html#5071" class="Field">arity</a> <a id="5176" class="Symbol">→</a> <a id="5178" href="Base.Complexity.CSP.html#4991" class="Bound">var</a>          <a id="5191" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5245" href="Base.Complexity.CSP.html#5245" class="Field">rel</a>    <a id="5252" class="Symbol">:</a> <a id="5254" href="Base.Relations.Continuous.html#4364" class="Function">ΠΡ[</a> <a id="5258" href="Base.Complexity.CSP.html#5258" class="Bound">i</a> <a id="5260" href="Base.Relations.Continuous.html#4364" class="Function">∈</a> <a id="5262" href="Base.Complexity.CSP.html#5071" class="Field">arity</a> <a id="5268" href="Base.Relations.Continuous.html#4364" class="Function">]</a> <a id="5270" class="Symbol">(</a><a id="5271" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5279" class="Symbol">(</a><a id="5280" href="Base.Complexity.CSP.html#5006" class="Bound">dom</a> <a id="5284" class="Symbol">(</a><a id="5285" href="Base.Complexity.CSP.html#5161" class="Field">scope</a> <a id="5291" href="Base.Complexity.CSP.html#5258" class="Bound">i</a><a id="5292" class="Symbol">)))</a>   <a id="5298" class="Comment">-- The constraint relation.</a>

  <a id="5329" href="Base.Complexity.CSP.html#5329" class="Function">satisfies</a> <a id="5339" class="Symbol">:</a> <a id="5341" class="Symbol">(∀</a> <a id="5344" href="Base.Complexity.CSP.html#5344" class="Bound">v</a> <a id="5346" class="Symbol">→</a> <a id="5348" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5356" class="Symbol">(</a><a id="5357" href="Base.Complexity.CSP.html#5006" class="Bound">dom</a> <a id="5361" href="Base.Complexity.CSP.html#5344" class="Bound">v</a><a id="5362" class="Symbol">))</a> <a id="5365" class="Symbol">→</a> <a id="5367" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a>  <a id="5373" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5429" href="Base.Complexity.CSP.html#5329" class="Function">satisfies</a> <a id="5439" href="Base.Complexity.CSP.html#5439" class="Bound">f</a> <a id="5441" class="Symbol">=</a> <a id="5443" href="Base.Complexity.CSP.html#5245" class="Field">rel</a> <a id="5447" class="Symbol">(</a><a id="5448" href="Base.Complexity.CSP.html#5439" class="Bound">f</a> <a id="5450" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5452" href="Base.Complexity.CSP.html#5161" class="Field">scope</a><a id="5457" class="Symbol">)</a>      <a id="5464" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5551" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6398" class="Keyword">open</a> <a id="6403" href="Setoid.Algebras.Basic.html#2890" class="Module">Algebra</a>
 <a id="6412" class="Keyword">open</a> <a id="6417" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6425" class="Keyword">record</a> <a id="6432" href="Base.Complexity.CSP.html#6432" class="Record">CSPInstance</a> <a id="6444" class="Symbol">(</a><a id="6445" href="Base.Complexity.CSP.html#6445" class="Bound">var</a> <a id="6449" class="Symbol">:</a> <a id="6451" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6456" href="Base.Complexity.CSP.html#4857" class="Bound">ν</a><a id="6457" class="Symbol">)(</a><a id="6459" href="Base.Complexity.CSP.html#6459" class="Bound">𝒜</a> <a id="6461" class="Symbol">:</a> <a id="6463" href="Base.Complexity.CSP.html#6445" class="Bound">var</a> <a id="6467" class="Symbol">→</a> <a id="6469" href="Setoid.Algebras.Basic.html#2890" class="Record">Algebra</a> <a id="6477" href="Base.Complexity.CSP.html#4909" class="Bound">α</a> <a id="6479" href="Base.Complexity.CSP.html#4911" class="Bound">ℓ</a><a id="6480" class="Symbol">)</a> <a id="6482" class="Symbol">:</a> <a id="6484" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6489" class="Symbol">(</a><a id="6490" href="Base.Complexity.CSP.html#4857" class="Bound">ν</a> <a id="6492" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6494" href="Base.Complexity.CSP.html#4909" class="Bound">α</a> <a id="6496" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6498" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6503" href="Base.Complexity.CSP.html#4795" class="Bound">ι</a><a id="6504" class="Symbol">)</a> <a id="6506" class="Keyword">where</a>
  <a id="6514" class="Keyword">field</a>
   <a id="6523" href="Base.Complexity.CSP.html#6523" class="Field">ar</a> <a id="6526" class="Symbol">:</a> <a id="6528" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6533" href="Base.Complexity.CSP.html#4795" class="Bound">ι</a>       <a id="6541" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6589" href="Base.Complexity.CSP.html#6589" class="Field">cs</a> <a id="6592" class="Symbol">:</a> <a id="6594" class="Symbol">(</a><a id="6595" href="Base.Complexity.CSP.html#6595" class="Bound">i</a> <a id="6597" class="Symbol">:</a> <a id="6599" href="Base.Complexity.CSP.html#6523" class="Field">ar</a><a id="6601" class="Symbol">)</a> <a id="6603" class="Symbol">→</a> <a id="6605" href="Base.Complexity.CSP.html#4979" class="Record">Constraint</a> <a id="6616" href="Base.Complexity.CSP.html#6445" class="Bound">var</a> <a id="6620" class="Symbol">(λ</a> <a id="6623" href="Base.Complexity.CSP.html#6623" class="Bound">v</a> <a id="6625" class="Symbol">→</a> <a id="6627" href="Setoid.Algebras.Basic.html#2947" class="Field">Domain</a> <a id="6634" class="Symbol">(</a><a id="6635" href="Base.Complexity.CSP.html#6459" class="Bound">𝒜</a> <a id="6637" href="Base.Complexity.CSP.html#6623" class="Bound">v</a><a id="6638" class="Symbol">))</a>

  <a id="6644" href="Base.Complexity.CSP.html#6644" class="Function">isSolution</a> <a id="6655" class="Symbol">:</a> <a id="6657" class="Symbol">(∀</a> <a id="6660" href="Base.Complexity.CSP.html#6660" class="Bound">v</a> <a id="6662" class="Symbol">→</a> <a id="6664" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6672" class="Symbol">(</a><a id="6673" href="Setoid.Algebras.Basic.html#2947" class="Field">Domain</a> <a id="6680" class="Symbol">(</a><a id="6681" href="Base.Complexity.CSP.html#6459" class="Bound">𝒜</a> <a id="6683" href="Base.Complexity.CSP.html#6660" class="Bound">v</a><a id="6684" class="Symbol">)))</a> <a id="6688" class="Symbol">→</a> <a id="6690" href="Base.Complexity.CSP.html#3707" class="Primitive">Type</a> <a id="6695" class="Symbol">_</a>  <a id="6698" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6739" href="Base.Complexity.CSP.html#6644" class="Function">isSolution</a> <a id="6750" href="Base.Complexity.CSP.html#6750" class="Bound">f</a> <a id="6752" class="Symbol">=</a> <a id="6754" class="Symbol">∀</a> <a id="6756" href="Base.Complexity.CSP.html#6756" class="Bound">i</a> <a id="6758" class="Symbol">→</a> <a id="6760" class="Symbol">(</a><a id="6761" href="Base.Complexity.CSP.html#5329" class="Function">Constraint.satisfies</a> <a id="6782" class="Symbol">(</a><a id="6783" href="Base.Complexity.CSP.html#6589" class="Field">cs</a> <a id="6786" href="Base.Complexity.CSP.html#6756" class="Bound">i</a><a id="6787" class="Symbol">))</a> <a id="6790" href="Base.Complexity.CSP.html#6750" class="Bound">f</a>  <a id="6793" class="Comment">-- if it satisfies all the constraints.</a>

</pre>

--------------------------------

<span>[← Base.Complexity.Basic](Base.Complexity.Basic.html)</span>
<span style="float:right;">[Top ↑](index.html)</span>

{% include UALib.Links.md %}
