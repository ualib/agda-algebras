---
layout: default
title : "Complexity.CSP module (The Agda Universal Algebra Library)"
date : "2021-07-14"
author: "the agda-algebras development team"
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

<a id="3375" class="Symbol">{-#</a> <a id="3379" class="Keyword">OPTIONS</a> <a id="3387" class="Pragma">--without-K</a> <a id="3399" class="Pragma">--exact-split</a> <a id="3413" class="Pragma">--safe</a> <a id="3420" class="Symbol">#-}</a>

<a id="3425" class="Keyword">open</a> <a id="3430" class="Keyword">import</a> <a id="3437" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3452" class="Keyword">using</a> <a id="3458" class="Symbol">(</a> <a id="3460" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="3462" class="Symbol">;</a> <a id="3464" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a> <a id="3466" class="Symbol">;</a> <a id="3468" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="3478" class="Symbol">)</a>

<a id="3481" class="Keyword">module</a> <a id="3488" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3503" class="Symbol">{</a><a id="3504" href="Complexity.CSP.html#3504" class="Bound">𝑆</a> <a id="3506" class="Symbol">:</a> <a id="3508" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="3518" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="3520" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a><a id="3521" class="Symbol">}</a> <a id="3523" class="Keyword">where</a>

<a id="3530" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3612" class="Keyword">open</a> <a id="3617" class="Keyword">import</a> <a id="3624" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3641" class="Keyword">using</a> <a id="3647" class="Symbol">(</a> <a id="3649" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3653" class="Symbol">;</a> <a id="3655" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3660" class="Symbol">;</a> <a id="3662" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3667" class="Symbol">)</a> <a id="3669" class="Keyword">renaming</a> <a id="3678" class="Symbol">(</a> <a id="3680" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3684" class="Symbol">to</a> <a id="3687" class="Primitive">Type</a> <a id="3692" class="Symbol">)</a>
<a id="3694" class="Keyword">open</a> <a id="3699" class="Keyword">import</a> <a id="3706" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3723" class="Keyword">using</a> <a id="3729" class="Symbol">(</a> <a id="3731" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3735" class="Symbol">)</a>
<a id="3737" class="Keyword">open</a> <a id="3742" class="Keyword">import</a> <a id="3749" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3766" class="Keyword">using</a> <a id="3772" class="Symbol">(</a> <a id="3774" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3781" class="Symbol">)</a>

<a id="3784" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3866" class="Keyword">open</a> <a id="3871" class="Keyword">import</a> <a id="3878" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>        <a id="3906" class="Keyword">using</a> <a id="3912" class="Symbol">(</a> <a id="3914" href="Relations.Continuous.html#4226" class="Function">ΠΡ</a> <a id="3917" class="Symbol">;</a> <a id="3919" href="Relations.Continuous.html#4334" class="Function">ΠΡ-syntax</a> <a id="3929" class="Symbol">)</a>
<a id="3931" class="Keyword">open</a> <a id="3936" class="Keyword">import</a> <a id="3943" href="Algebras.Func.Basic.html" class="Module">Algebras.Func.Basic</a> <a id="3963" class="Symbol">{</a><a id="3964" class="Argument">𝑆</a> <a id="3966" class="Symbol">=</a> <a id="3968" href="Complexity.CSP.html#3504" class="Bound">𝑆</a><a id="3969" class="Symbol">}</a> <a id="3971" class="Keyword">using</a> <a id="3977" class="Symbol">(</a> <a id="3979" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="3993" class="Symbol">)</a>

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

<a id="4722" class="Keyword">module</a> <a id="4729" href="Complexity.CSP.html#4729" class="Module">_</a> <a id="4731" class="Comment">-- levels for...</a>
         <a id="4757" class="Symbol">{</a><a id="4758" href="Complexity.CSP.html#4758" class="Bound">ι</a> <a id="4760" class="Symbol">:</a> <a id="4762" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4767" class="Symbol">}</a> <a id="4769" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4816" class="Symbol">{</a><a id="4817" href="Complexity.CSP.html#4817" class="Bound">ν</a> <a id="4819" class="Symbol">:</a> <a id="4821" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4826" class="Symbol">}</a> <a id="4828" class="Comment">-- ...variable symbol types</a>
         <a id="4865" class="Symbol">{</a><a id="4866" href="Complexity.CSP.html#4866" class="Bound">α</a> <a id="4868" href="Complexity.CSP.html#4868" class="Bound">ℓ</a> <a id="4870" class="Symbol">:</a> <a id="4872" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4877" class="Symbol">}</a> <a id="4879" class="Comment">-- ... domain types</a>
         <a id="4908" class="Keyword">where</a>
 <a id="4915" class="Keyword">open</a> <a id="4920" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4928" class="Keyword">record</a> <a id="4935" href="Complexity.CSP.html#4935" class="Record">Constraint</a> <a id="4946" class="Symbol">(</a><a id="4947" href="Complexity.CSP.html#4947" class="Bound">var</a> <a id="4951" class="Symbol">:</a> <a id="4953" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="4958" href="Complexity.CSP.html#4817" class="Bound">ν</a><a id="4959" class="Symbol">)</a> <a id="4961" class="Symbol">(</a><a id="4962" href="Complexity.CSP.html#4962" class="Bound">dom</a> <a id="4966" class="Symbol">:</a> <a id="4968" href="Complexity.CSP.html#4947" class="Bound">var</a> <a id="4972" class="Symbol">→</a> <a id="4974" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4981" href="Complexity.CSP.html#4866" class="Bound">α</a> <a id="4983" href="Complexity.CSP.html#4868" class="Bound">ℓ</a><a id="4984" class="Symbol">)</a> <a id="4986" class="Symbol">:</a> <a id="4988" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="4993" class="Symbol">(</a><a id="4994" href="Complexity.CSP.html#4817" class="Bound">ν</a> <a id="4996" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4998" href="Complexity.CSP.html#4866" class="Bound">α</a> <a id="5000" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5002" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="5007" href="Complexity.CSP.html#4758" class="Bound">ι</a><a id="5008" class="Symbol">)</a> <a id="5010" class="Keyword">where</a>
  <a id="5018" class="Keyword">field</a>
   <a id="5027" href="Complexity.CSP.html#5027" class="Field">arity</a>  <a id="5034" class="Symbol">:</a> <a id="5036" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="5041" href="Complexity.CSP.html#4758" class="Bound">ι</a>               <a id="5057" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5117" href="Complexity.CSP.html#5117" class="Field">scope</a>  <a id="5124" class="Symbol">:</a> <a id="5126" href="Complexity.CSP.html#5027" class="Field">arity</a> <a id="5132" class="Symbol">→</a> <a id="5134" href="Complexity.CSP.html#4947" class="Bound">var</a>          <a id="5147" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5201" href="Complexity.CSP.html#5201" class="Field">rel</a>    <a id="5208" class="Symbol">:</a> <a id="5210" href="Relations.Continuous.html#4334" class="Function">ΠΡ[</a> <a id="5214" href="Complexity.CSP.html#5214" class="Bound">i</a> <a id="5216" href="Relations.Continuous.html#4334" class="Function">∈</a> <a id="5218" href="Complexity.CSP.html#5027" class="Field">arity</a> <a id="5224" href="Relations.Continuous.html#4334" class="Function">]</a> <a id="5226" class="Symbol">(</a><a id="5227" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5235" class="Symbol">(</a><a id="5236" href="Complexity.CSP.html#4962" class="Bound">dom</a> <a id="5240" class="Symbol">(</a><a id="5241" href="Complexity.CSP.html#5117" class="Field">scope</a> <a id="5247" href="Complexity.CSP.html#5214" class="Bound">i</a><a id="5248" class="Symbol">)))</a>     <a id="5256" class="Comment">-- The constraint relation.</a>

  <a id="5287" href="Complexity.CSP.html#5287" class="Function">satisfies</a> <a id="5297" class="Symbol">:</a> <a id="5299" class="Symbol">(∀</a> <a id="5302" href="Complexity.CSP.html#5302" class="Bound">v</a> <a id="5304" class="Symbol">→</a> <a id="5306" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5314" class="Symbol">(</a><a id="5315" href="Complexity.CSP.html#4962" class="Bound">dom</a> <a id="5319" href="Complexity.CSP.html#5302" class="Bound">v</a><a id="5320" class="Symbol">))</a> <a id="5323" class="Symbol">→</a> <a id="5325" href="Complexity.CSP.html#3687" class="Primitive">Type</a>  <a id="5331" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5387" href="Complexity.CSP.html#5287" class="Function">satisfies</a> <a id="5397" href="Complexity.CSP.html#5397" class="Bound">f</a> <a id="5399" class="Symbol">=</a> <a id="5401" href="Complexity.CSP.html#5201" class="Field">rel</a> <a id="5405" class="Symbol">(</a><a id="5406" href="Complexity.CSP.html#5397" class="Bound">f</a> <a id="5408" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5410" href="Complexity.CSP.html#5117" class="Field">scope</a><a id="5415" class="Symbol">)</a>      <a id="5422" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5509" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6362" class="Keyword">open</a> <a id="6367" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a>
 <a id="6382" class="Keyword">open</a> <a id="6387" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6395" class="Keyword">record</a> <a id="6402" href="Complexity.CSP.html#6402" class="Record">CSPInstance</a> <a id="6414" class="Symbol">(</a><a id="6415" href="Complexity.CSP.html#6415" class="Bound">var</a> <a id="6419" class="Symbol">:</a> <a id="6421" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6426" href="Complexity.CSP.html#4817" class="Bound">ν</a><a id="6427" class="Symbol">)(</a><a id="6429" href="Complexity.CSP.html#6429" class="Bound">𝒜</a> <a id="6431" class="Symbol">:</a> <a id="6433" href="Complexity.CSP.html#6415" class="Bound">var</a> <a id="6437" class="Symbol">→</a> <a id="6439" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="6453" href="Complexity.CSP.html#4866" class="Bound">α</a> <a id="6455" href="Complexity.CSP.html#4868" class="Bound">ℓ</a><a id="6456" class="Symbol">)</a> <a id="6458" class="Symbol">:</a> <a id="6460" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6465" class="Symbol">(</a><a id="6466" href="Complexity.CSP.html#4817" class="Bound">ν</a> <a id="6468" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6470" href="Complexity.CSP.html#4866" class="Bound">α</a> <a id="6472" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6474" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6479" href="Complexity.CSP.html#4758" class="Bound">ι</a><a id="6480" class="Symbol">)</a> <a id="6482" class="Keyword">where</a>
  <a id="6490" class="Keyword">field</a>
   <a id="6499" href="Complexity.CSP.html#6499" class="Field">ar</a> <a id="6502" class="Symbol">:</a> <a id="6504" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6509" href="Complexity.CSP.html#4758" class="Bound">ι</a>       <a id="6517" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6565" href="Complexity.CSP.html#6565" class="Field">cs</a> <a id="6568" class="Symbol">:</a> <a id="6570" class="Symbol">(</a><a id="6571" href="Complexity.CSP.html#6571" class="Bound">i</a> <a id="6573" class="Symbol">:</a> <a id="6575" href="Complexity.CSP.html#6499" class="Field">ar</a><a id="6577" class="Symbol">)</a> <a id="6579" class="Symbol">→</a> <a id="6581" href="Complexity.CSP.html#4935" class="Record">Constraint</a> <a id="6592" href="Complexity.CSP.html#6415" class="Bound">var</a> <a id="6596" class="Symbol">(λ</a> <a id="6599" href="Complexity.CSP.html#6599" class="Bound">v</a> <a id="6601" class="Symbol">→</a> <a id="6603" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="6610" class="Symbol">(</a><a id="6611" href="Complexity.CSP.html#6429" class="Bound">𝒜</a> <a id="6613" href="Complexity.CSP.html#6599" class="Bound">v</a><a id="6614" class="Symbol">))</a>

  <a id="6620" href="Complexity.CSP.html#6620" class="Function">isSolution</a> <a id="6631" class="Symbol">:</a> <a id="6633" class="Symbol">(∀</a> <a id="6636" href="Complexity.CSP.html#6636" class="Bound">v</a> <a id="6638" class="Symbol">→</a> <a id="6640" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6648" class="Symbol">(</a><a id="6649" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="6656" class="Symbol">(</a><a id="6657" href="Complexity.CSP.html#6429" class="Bound">𝒜</a> <a id="6659" href="Complexity.CSP.html#6636" class="Bound">v</a><a id="6660" class="Symbol">)))</a> <a id="6664" class="Symbol">→</a> <a id="6666" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6671" class="Symbol">_</a>  <a id="6674" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6715" href="Complexity.CSP.html#6620" class="Function">isSolution</a> <a id="6726" href="Complexity.CSP.html#6726" class="Bound">f</a> <a id="6728" class="Symbol">=</a> <a id="6730" class="Symbol">∀</a> <a id="6732" href="Complexity.CSP.html#6732" class="Bound">i</a> <a id="6734" class="Symbol">→</a> <a id="6736" class="Symbol">(</a><a id="6737" href="Complexity.CSP.html#5287" class="Function">Constraint.satisfies</a> <a id="6758" class="Symbol">(</a><a id="6759" href="Complexity.CSP.html#6565" class="Field">cs</a> <a id="6762" href="Complexity.CSP.html#6732" class="Bound">i</a><a id="6763" class="Symbol">))</a> <a id="6766" href="Complexity.CSP.html#6726" class="Bound">f</a>  <a id="6769" class="Comment">-- if it satisfies all the constraints.</a>

</pre>

--------------------------------

<span>[← Complexity.Basic](Complexity.Basic.html)</span>
<span style="float:right;">[agda-algebras ↑](agda-algebras.html)</span>

{% include UALib.Links.md %}
