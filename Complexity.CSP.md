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

<a id="3425" class="Keyword">open</a> <a id="3430" class="Keyword">import</a> <a id="3437" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3452" class="Keyword">using</a> <a id="3458" class="Symbol">(</a> <a id="3460" href="Algebras.Basic.html#1142" class="Generalizable">𝓞</a> <a id="3462" class="Symbol">;</a> <a id="3464" href="Algebras.Basic.html#1144" class="Generalizable">𝓥</a> <a id="3466" class="Symbol">;</a> <a id="3468" href="Algebras.Basic.html#3870" class="Function">Signature</a> <a id="3478" class="Symbol">)</a>

<a id="3481" class="Keyword">module</a> <a id="3488" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3503" class="Symbol">{</a><a id="3504" href="Complexity.CSP.html#3504" class="Bound">𝑆</a> <a id="3506" class="Symbol">:</a> <a id="3508" href="Algebras.Basic.html#3870" class="Function">Signature</a> <a id="3518" href="Algebras.Basic.html#1142" class="Generalizable">𝓞</a> <a id="3520" href="Algebras.Basic.html#1144" class="Generalizable">𝓥</a><a id="3521" class="Symbol">}</a> <a id="3523" class="Keyword">where</a>

<a id="3530" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3612" class="Keyword">open</a> <a id="3617" class="Keyword">import</a> <a id="3624" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3641" class="Keyword">using</a> <a id="3647" class="Symbol">(</a> <a id="3649" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3653" class="Symbol">;</a> <a id="3655" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3660" class="Symbol">;</a> <a id="3662" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3667" class="Symbol">)</a> <a id="3669" class="Keyword">renaming</a> <a id="3678" class="Symbol">(</a> <a id="3680" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3684" class="Symbol">to</a> <a id="3687" class="Primitive">Type</a> <a id="3692" class="Symbol">)</a>
<a id="3694" class="Keyword">open</a> <a id="3699" class="Keyword">import</a> <a id="3706" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3723" class="Keyword">using</a> <a id="3729" class="Symbol">(</a> <a id="3731" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3735" class="Symbol">)</a>
<a id="3737" class="Keyword">open</a> <a id="3742" class="Keyword">import</a> <a id="3749" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3766" class="Keyword">using</a> <a id="3772" class="Symbol">(</a> <a id="3774" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3781" class="Symbol">)</a>

<a id="3784" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3866" class="Keyword">open</a> <a id="3871" class="Keyword">import</a> <a id="3878" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3902" class="Keyword">using</a> <a id="3908" class="Symbol">(</a> <a id="3910" href="Relations.Continuous.html#4226" class="Function">ΠΡ</a> <a id="3913" class="Symbol">;</a> <a id="3915" href="Relations.Continuous.html#4334" class="Function">ΠΡ-syntax</a> <a id="3925" class="Symbol">)</a>
<a id="3927" class="Keyword">open</a> <a id="3932" class="Keyword">import</a> <a id="3939" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3961" class="Symbol">{</a><a id="3962" class="Argument">𝑆</a> <a id="3964" class="Symbol">=</a> <a id="3966" href="Complexity.CSP.html#3504" class="Bound">𝑆</a><a id="3967" class="Symbol">}</a> <a id="3969" class="Keyword">using</a> <a id="3975" class="Symbol">(</a> <a id="3977" href="Algebras.Setoid.Basic.html#3242" class="Record">SetoidAlgebra</a> <a id="3991" class="Symbol">)</a>

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

<a id="4720" class="Keyword">module</a> <a id="4727" href="Complexity.CSP.html#4727" class="Module">_</a> <a id="4729" class="Comment">-- levels for...</a>
         <a id="4755" class="Symbol">{</a><a id="4756" href="Complexity.CSP.html#4756" class="Bound">ι</a> <a id="4758" class="Symbol">:</a> <a id="4760" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4765" class="Symbol">}</a> <a id="4767" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4814" class="Symbol">{</a><a id="4815" href="Complexity.CSP.html#4815" class="Bound">ν</a> <a id="4817" class="Symbol">:</a> <a id="4819" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4824" class="Symbol">}</a> <a id="4826" class="Comment">-- ...variable symbol types</a>
         <a id="4863" class="Symbol">{</a><a id="4864" href="Complexity.CSP.html#4864" class="Bound">α</a> <a id="4866" href="Complexity.CSP.html#4866" class="Bound">ℓ</a> <a id="4868" class="Symbol">:</a> <a id="4870" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4875" class="Symbol">}</a> <a id="4877" class="Comment">-- ... domain types</a>
         <a id="4906" class="Keyword">where</a>
 <a id="4913" class="Keyword">open</a> <a id="4918" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4926" class="Keyword">record</a> <a id="4933" href="Complexity.CSP.html#4933" class="Record">Constraint</a> <a id="4944" class="Symbol">(</a><a id="4945" href="Complexity.CSP.html#4945" class="Bound">var</a> <a id="4949" class="Symbol">:</a> <a id="4951" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="4956" href="Complexity.CSP.html#4815" class="Bound">ν</a><a id="4957" class="Symbol">)</a> <a id="4959" class="Symbol">(</a><a id="4960" href="Complexity.CSP.html#4960" class="Bound">dom</a> <a id="4964" class="Symbol">:</a> <a id="4966" href="Complexity.CSP.html#4945" class="Bound">var</a> <a id="4970" class="Symbol">→</a> <a id="4972" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4979" href="Complexity.CSP.html#4864" class="Bound">α</a> <a id="4981" href="Complexity.CSP.html#4866" class="Bound">ℓ</a><a id="4982" class="Symbol">)</a> <a id="4984" class="Symbol">:</a> <a id="4986" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="4991" class="Symbol">(</a><a id="4992" href="Complexity.CSP.html#4815" class="Bound">ν</a> <a id="4994" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4996" href="Complexity.CSP.html#4864" class="Bound">α</a> <a id="4998" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="5000" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="5005" href="Complexity.CSP.html#4756" class="Bound">ι</a><a id="5006" class="Symbol">)</a> <a id="5008" class="Keyword">where</a>
  <a id="5016" class="Keyword">field</a>
   <a id="5025" href="Complexity.CSP.html#5025" class="Field">arity</a>  <a id="5032" class="Symbol">:</a> <a id="5034" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="5039" href="Complexity.CSP.html#4756" class="Bound">ι</a>               <a id="5055" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5115" href="Complexity.CSP.html#5115" class="Field">scope</a>  <a id="5122" class="Symbol">:</a> <a id="5124" href="Complexity.CSP.html#5025" class="Field">arity</a> <a id="5130" class="Symbol">→</a> <a id="5132" href="Complexity.CSP.html#4945" class="Bound">var</a>          <a id="5145" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5199" href="Complexity.CSP.html#5199" class="Field">rel</a>    <a id="5206" class="Symbol">:</a> <a id="5208" href="Relations.Continuous.html#4334" class="Function">ΠΡ[</a> <a id="5212" href="Complexity.CSP.html#5212" class="Bound">i</a> <a id="5214" href="Relations.Continuous.html#4334" class="Function">∈</a> <a id="5216" href="Complexity.CSP.html#5025" class="Field">arity</a> <a id="5222" href="Relations.Continuous.html#4334" class="Function">]</a> <a id="5224" class="Symbol">(</a><a id="5225" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5233" class="Symbol">(</a><a id="5234" href="Complexity.CSP.html#4960" class="Bound">dom</a> <a id="5238" class="Symbol">(</a><a id="5239" href="Complexity.CSP.html#5115" class="Field">scope</a> <a id="5245" href="Complexity.CSP.html#5212" class="Bound">i</a><a id="5246" class="Symbol">)))</a>     <a id="5254" class="Comment">-- The constraint relation.</a>

  <a id="5285" href="Complexity.CSP.html#5285" class="Function">satisfies</a> <a id="5295" class="Symbol">:</a> <a id="5297" class="Symbol">(∀</a> <a id="5300" href="Complexity.CSP.html#5300" class="Bound">v</a> <a id="5302" class="Symbol">→</a> <a id="5304" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5312" class="Symbol">(</a><a id="5313" href="Complexity.CSP.html#4960" class="Bound">dom</a> <a id="5317" href="Complexity.CSP.html#5300" class="Bound">v</a><a id="5318" class="Symbol">))</a> <a id="5321" class="Symbol">→</a> <a id="5323" href="Complexity.CSP.html#3687" class="Primitive">Type</a>  <a id="5329" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5385" href="Complexity.CSP.html#5285" class="Function">satisfies</a> <a id="5395" href="Complexity.CSP.html#5395" class="Bound">f</a> <a id="5397" class="Symbol">=</a> <a id="5399" href="Complexity.CSP.html#5199" class="Field">rel</a> <a id="5403" class="Symbol">(</a><a id="5404" href="Complexity.CSP.html#5395" class="Bound">f</a> <a id="5406" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5408" href="Complexity.CSP.html#5115" class="Field">scope</a><a id="5413" class="Symbol">)</a>      <a id="5420" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5507" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6360" class="Keyword">open</a> <a id="6365" href="Algebras.Setoid.Basic.html#3242" class="Module">SetoidAlgebra</a>
 <a id="6380" class="Keyword">open</a> <a id="6385" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6393" class="Keyword">record</a> <a id="6400" href="Complexity.CSP.html#6400" class="Record">CSPInstance</a> <a id="6412" class="Symbol">(</a><a id="6413" href="Complexity.CSP.html#6413" class="Bound">var</a> <a id="6417" class="Symbol">:</a> <a id="6419" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6424" href="Complexity.CSP.html#4815" class="Bound">ν</a><a id="6425" class="Symbol">)(</a><a id="6427" href="Complexity.CSP.html#6427" class="Bound">𝒜</a> <a id="6429" class="Symbol">:</a> <a id="6431" href="Complexity.CSP.html#6413" class="Bound">var</a> <a id="6435" class="Symbol">→</a> <a id="6437" href="Algebras.Setoid.Basic.html#3242" class="Record">SetoidAlgebra</a> <a id="6451" href="Complexity.CSP.html#4864" class="Bound">α</a> <a id="6453" href="Complexity.CSP.html#4866" class="Bound">ℓ</a><a id="6454" class="Symbol">)</a> <a id="6456" class="Symbol">:</a> <a id="6458" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6463" class="Symbol">(</a><a id="6464" href="Complexity.CSP.html#4815" class="Bound">ν</a> <a id="6466" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6468" href="Complexity.CSP.html#4864" class="Bound">α</a> <a id="6470" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6472" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6477" href="Complexity.CSP.html#4756" class="Bound">ι</a><a id="6478" class="Symbol">)</a> <a id="6480" class="Keyword">where</a>
  <a id="6488" class="Keyword">field</a>
   <a id="6497" href="Complexity.CSP.html#6497" class="Field">ar</a> <a id="6500" class="Symbol">:</a> <a id="6502" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6507" href="Complexity.CSP.html#4756" class="Bound">ι</a>       <a id="6515" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6563" href="Complexity.CSP.html#6563" class="Field">cs</a> <a id="6566" class="Symbol">:</a> <a id="6568" class="Symbol">(</a><a id="6569" href="Complexity.CSP.html#6569" class="Bound">i</a> <a id="6571" class="Symbol">:</a> <a id="6573" href="Complexity.CSP.html#6497" class="Field">ar</a><a id="6575" class="Symbol">)</a> <a id="6577" class="Symbol">→</a> <a id="6579" href="Complexity.CSP.html#4933" class="Record">Constraint</a> <a id="6590" href="Complexity.CSP.html#6413" class="Bound">var</a> <a id="6594" class="Symbol">(λ</a> <a id="6597" href="Complexity.CSP.html#6597" class="Bound">v</a> <a id="6599" class="Symbol">→</a> <a id="6601" href="Algebras.Setoid.Basic.html#3305" class="Field">Domain</a> <a id="6608" class="Symbol">(</a><a id="6609" href="Complexity.CSP.html#6427" class="Bound">𝒜</a> <a id="6611" href="Complexity.CSP.html#6597" class="Bound">v</a><a id="6612" class="Symbol">))</a>

  <a id="6618" href="Complexity.CSP.html#6618" class="Function">isSolution</a> <a id="6629" class="Symbol">:</a> <a id="6631" class="Symbol">(∀</a> <a id="6634" href="Complexity.CSP.html#6634" class="Bound">v</a> <a id="6636" class="Symbol">→</a> <a id="6638" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6646" class="Symbol">(</a><a id="6647" href="Algebras.Setoid.Basic.html#3305" class="Field">Domain</a> <a id="6654" class="Symbol">(</a><a id="6655" href="Complexity.CSP.html#6427" class="Bound">𝒜</a> <a id="6657" href="Complexity.CSP.html#6634" class="Bound">v</a><a id="6658" class="Symbol">)))</a> <a id="6662" class="Symbol">→</a> <a id="6664" href="Complexity.CSP.html#3687" class="Primitive">Type</a> <a id="6669" class="Symbol">_</a>  <a id="6672" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6713" href="Complexity.CSP.html#6618" class="Function">isSolution</a> <a id="6724" href="Complexity.CSP.html#6724" class="Bound">f</a> <a id="6726" class="Symbol">=</a> <a id="6728" class="Symbol">∀</a> <a id="6730" href="Complexity.CSP.html#6730" class="Bound">i</a> <a id="6732" class="Symbol">→</a> <a id="6734" class="Symbol">(</a><a id="6735" href="Complexity.CSP.html#5285" class="Function">Constraint.satisfies</a> <a id="6756" class="Symbol">(</a><a id="6757" href="Complexity.CSP.html#6563" class="Field">cs</a> <a id="6760" href="Complexity.CSP.html#6730" class="Bound">i</a><a id="6761" class="Symbol">))</a> <a id="6764" href="Complexity.CSP.html#6724" class="Bound">f</a>  <a id="6767" class="Comment">-- if it satisfies all the constraints.</a>

</pre>

--------------------------------

<span>[← Complexity.Basic](Complexity.Basic.html)</span>
<span style="float:right;">[agda-algebras ↑](agda-algebras.html)</span>

{% include UALib.Links.md %}
