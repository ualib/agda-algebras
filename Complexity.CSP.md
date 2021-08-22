---
layout: default
title : Complexity.CSP module (The Agda Universal Algebra Library)
date : 2021-07-14
author: [agda-algebras development team][]
---

### Constraint Satisfaction Problems

#### The relational formulation of CSP

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



#### Connection to algebraic CSP

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

<a id="3157" class="Symbol">{-#</a> <a id="3161" class="Keyword">OPTIONS</a> <a id="3169" class="Pragma">--without-K</a> <a id="3181" class="Pragma">--exact-split</a> <a id="3195" class="Pragma">--safe</a> <a id="3202" class="Symbol">#-}</a>

<a id="3207" class="Keyword">open</a> <a id="3212" class="Keyword">import</a> <a id="3219" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3234" class="Keyword">using</a> <a id="3240" class="Symbol">(</a> <a id="3242" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="3244" class="Symbol">;</a> <a id="3246" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a> <a id="3248" class="Symbol">;</a> <a id="3250" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="3260" class="Symbol">)</a>

<a id="3263" class="Keyword">module</a> <a id="3270" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3285" class="Symbol">{</a><a id="3286" href="Complexity.CSP.html#3286" class="Bound">𝑆</a> <a id="3288" class="Symbol">:</a> <a id="3290" href="Algebras.Basic.html#3576" class="Function">Signature</a> <a id="3300" href="Algebras.Basic.html#1210" class="Generalizable">𝓞</a> <a id="3302" href="Algebras.Basic.html#1212" class="Generalizable">𝓥</a><a id="3303" class="Symbol">}</a> <a id="3305" class="Keyword">where</a>

<a id="3312" class="Keyword">open</a> <a id="3317" class="Keyword">import</a> <a id="3324" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3341" class="Keyword">using</a> <a id="3347" class="Symbol">(</a> <a id="3349" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3353" class="Symbol">;</a> <a id="3355" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3360" class="Symbol">;</a> <a id="3362" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3367" class="Symbol">)</a> <a id="3369" class="Keyword">renaming</a> <a id="3378" class="Symbol">(</a> <a id="3380" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3384" class="Symbol">to</a> <a id="3387" class="Primitive">Type</a> <a id="3392" class="Symbol">)</a>
<a id="3394" class="Keyword">open</a> <a id="3399" class="Keyword">import</a> <a id="3406" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3423" class="Keyword">using</a> <a id="3429" class="Symbol">(</a> <a id="3431" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3435" class="Symbol">)</a>
<a id="3437" class="Keyword">open</a> <a id="3442" class="Keyword">import</a> <a id="3449" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3466" class="Keyword">using</a> <a id="3472" class="Symbol">(</a> <a id="3474" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3481" class="Symbol">)</a>


<a id="3485" class="Keyword">open</a> <a id="3490" class="Keyword">import</a> <a id="3497" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3521" class="Keyword">using</a> <a id="3527" class="Symbol">(</a> <a id="3529" href="Relations.Continuous.html#4087" class="Function">ΠΡ</a> <a id="3532" class="Symbol">;</a> <a id="3534" href="Relations.Continuous.html#4195" class="Function">ΠΡ-syntax</a> <a id="3544" class="Symbol">)</a>
<a id="3546" class="Keyword">open</a> <a id="3551" class="Keyword">import</a> <a id="3558" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3580" class="Symbol">{</a><a id="3581" class="Argument">𝑆</a> <a id="3583" class="Symbol">=</a> <a id="3585" href="Complexity.CSP.html#3286" class="Bound">𝑆</a><a id="3586" class="Symbol">}</a> <a id="3588" class="Keyword">using</a> <a id="3594" class="Symbol">(</a> <a id="3596" href="Algebras.Setoid.Basic.html#3113" class="Record">SetoidAlgebra</a> <a id="3610" class="Symbol">)</a>


</pre>

#### Constraints

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

<a id="4319" class="Keyword">module</a> <a id="4326" href="Complexity.CSP.html#4326" class="Module">_</a> <a id="4328" class="Comment">-- levels for...</a>
         <a id="4354" class="Symbol">{</a><a id="4355" href="Complexity.CSP.html#4355" class="Bound">ι</a> <a id="4357" class="Symbol">:</a> <a id="4359" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4364" class="Symbol">}</a> <a id="4366" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4413" class="Symbol">{</a><a id="4414" href="Complexity.CSP.html#4414" class="Bound">ν</a> <a id="4416" class="Symbol">:</a> <a id="4418" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4423" class="Symbol">}</a> <a id="4425" class="Comment">-- ...variable symbol types</a>
         <a id="4462" class="Symbol">{</a><a id="4463" href="Complexity.CSP.html#4463" class="Bound">α</a> <a id="4465" href="Complexity.CSP.html#4465" class="Bound">ℓ</a> <a id="4467" class="Symbol">:</a> <a id="4469" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4474" class="Symbol">}</a> <a id="4476" class="Comment">-- ... domain types</a>
         <a id="4505" class="Keyword">where</a>
 <a id="4512" class="Keyword">open</a> <a id="4517" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4525" class="Keyword">record</a> <a id="4532" href="Complexity.CSP.html#4532" class="Record">Constraint</a> <a id="4543" class="Symbol">(</a><a id="4544" href="Complexity.CSP.html#4544" class="Bound">var</a> <a id="4548" class="Symbol">:</a> <a id="4550" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="4555" href="Complexity.CSP.html#4414" class="Bound">ν</a><a id="4556" class="Symbol">)</a> <a id="4558" class="Symbol">(</a><a id="4559" href="Complexity.CSP.html#4559" class="Bound">dom</a> <a id="4563" class="Symbol">:</a> <a id="4565" href="Complexity.CSP.html#4544" class="Bound">var</a> <a id="4569" class="Symbol">→</a> <a id="4571" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4578" href="Complexity.CSP.html#4463" class="Bound">α</a> <a id="4580" href="Complexity.CSP.html#4465" class="Bound">ℓ</a><a id="4581" class="Symbol">)</a> <a id="4583" class="Symbol">:</a> <a id="4585" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="4590" class="Symbol">(</a><a id="4591" href="Complexity.CSP.html#4414" class="Bound">ν</a> <a id="4593" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4595" href="Complexity.CSP.html#4463" class="Bound">α</a> <a id="4597" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4599" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="4604" href="Complexity.CSP.html#4355" class="Bound">ι</a><a id="4605" class="Symbol">)</a> <a id="4607" class="Keyword">where</a>
  <a id="4615" class="Keyword">field</a>
   <a id="4624" href="Complexity.CSP.html#4624" class="Field">arity</a>  <a id="4631" class="Symbol">:</a> <a id="4633" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="4638" href="Complexity.CSP.html#4355" class="Bound">ι</a>               <a id="4654" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="4714" href="Complexity.CSP.html#4714" class="Field">scope</a>  <a id="4721" class="Symbol">:</a> <a id="4723" href="Complexity.CSP.html#4624" class="Field">arity</a> <a id="4729" class="Symbol">→</a> <a id="4731" href="Complexity.CSP.html#4544" class="Bound">var</a>          <a id="4744" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="4798" href="Complexity.CSP.html#4798" class="Field">rel</a>    <a id="4805" class="Symbol">:</a> <a id="4807" href="Relations.Continuous.html#4195" class="Function">ΠΡ[</a> <a id="4811" href="Complexity.CSP.html#4811" class="Bound">i</a> <a id="4813" href="Relations.Continuous.html#4195" class="Function">∈</a> <a id="4815" href="Complexity.CSP.html#4624" class="Field">arity</a> <a id="4821" href="Relations.Continuous.html#4195" class="Function">]</a> <a id="4823" class="Symbol">(</a><a id="4824" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="4832" class="Symbol">(</a><a id="4833" href="Complexity.CSP.html#4559" class="Bound">dom</a> <a id="4837" class="Symbol">(</a><a id="4838" href="Complexity.CSP.html#4714" class="Field">scope</a> <a id="4844" href="Complexity.CSP.html#4811" class="Bound">i</a><a id="4845" class="Symbol">)))</a>     <a id="4853" class="Comment">-- The constraint relation.</a>

  <a id="4884" href="Complexity.CSP.html#4884" class="Function">satisfies</a> <a id="4894" class="Symbol">:</a> <a id="4896" class="Symbol">(∀</a> <a id="4899" href="Complexity.CSP.html#4899" class="Bound">v</a> <a id="4901" class="Symbol">→</a> <a id="4903" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="4911" class="Symbol">(</a><a id="4912" href="Complexity.CSP.html#4559" class="Bound">dom</a> <a id="4916" href="Complexity.CSP.html#4899" class="Bound">v</a><a id="4917" class="Symbol">))</a> <a id="4920" class="Symbol">→</a> <a id="4922" href="Complexity.CSP.html#3387" class="Primitive">Type</a>  <a id="4928" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="4984" href="Complexity.CSP.html#4884" class="Function">satisfies</a> <a id="4994" href="Complexity.CSP.html#4994" class="Bound">f</a> <a id="4996" class="Symbol">=</a> <a id="4998" href="Complexity.CSP.html#4798" class="Field">rel</a> <a id="5002" class="Symbol">(</a><a id="5003" href="Complexity.CSP.html#4994" class="Bound">f</a> <a id="5005" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5007" href="Complexity.CSP.html#4714" class="Field">scope</a><a id="5012" class="Symbol">)</a>      <a id="5019" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5106" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
</pre>

#### CSP Templates and Instances

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
 <a id="5917" class="Keyword">open</a> <a id="5922" href="Algebras.Setoid.Basic.html#3113" class="Module">SetoidAlgebra</a>
 <a id="5937" class="Keyword">open</a> <a id="5942" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="5950" class="Keyword">record</a> <a id="5957" href="Complexity.CSP.html#5957" class="Record">CSPInstance</a> <a id="5969" class="Symbol">(</a><a id="5970" href="Complexity.CSP.html#5970" class="Bound">var</a> <a id="5974" class="Symbol">:</a> <a id="5976" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="5981" href="Complexity.CSP.html#4414" class="Bound">ν</a><a id="5982" class="Symbol">)(</a><a id="5984" href="Complexity.CSP.html#5984" class="Bound">𝒜</a> <a id="5986" class="Symbol">:</a> <a id="5988" href="Complexity.CSP.html#5970" class="Bound">var</a> <a id="5992" class="Symbol">→</a> <a id="5994" href="Algebras.Setoid.Basic.html#3113" class="Record">SetoidAlgebra</a> <a id="6008" href="Complexity.CSP.html#4463" class="Bound">α</a> <a id="6010" href="Complexity.CSP.html#4465" class="Bound">ℓ</a><a id="6011" class="Symbol">)</a> <a id="6013" class="Symbol">:</a> <a id="6015" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="6020" class="Symbol">(</a><a id="6021" href="Complexity.CSP.html#4414" class="Bound">ν</a> <a id="6023" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6025" href="Complexity.CSP.html#4463" class="Bound">α</a> <a id="6027" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6029" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6034" href="Complexity.CSP.html#4355" class="Bound">ι</a><a id="6035" class="Symbol">)</a> <a id="6037" class="Keyword">where</a>
  <a id="6045" class="Keyword">field</a>
   <a id="6054" href="Complexity.CSP.html#6054" class="Field">ar</a> <a id="6057" class="Symbol">:</a> <a id="6059" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="6064" href="Complexity.CSP.html#4355" class="Bound">ι</a>       <a id="6072" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6120" href="Complexity.CSP.html#6120" class="Field">cs</a> <a id="6123" class="Symbol">:</a> <a id="6125" class="Symbol">(</a><a id="6126" href="Complexity.CSP.html#6126" class="Bound">i</a> <a id="6128" class="Symbol">:</a> <a id="6130" href="Complexity.CSP.html#6054" class="Field">ar</a><a id="6132" class="Symbol">)</a> <a id="6134" class="Symbol">→</a> <a id="6136" href="Complexity.CSP.html#4532" class="Record">Constraint</a> <a id="6147" href="Complexity.CSP.html#5970" class="Bound">var</a> <a id="6151" class="Symbol">(λ</a> <a id="6154" href="Complexity.CSP.html#6154" class="Bound">v</a> <a id="6156" class="Symbol">→</a> <a id="6158" href="Algebras.Setoid.Basic.html#3179" class="Field">Domain</a> <a id="6165" class="Symbol">(</a><a id="6166" href="Complexity.CSP.html#5984" class="Bound">𝒜</a> <a id="6168" href="Complexity.CSP.html#6154" class="Bound">v</a><a id="6169" class="Symbol">))</a>

  <a id="6175" href="Complexity.CSP.html#6175" class="Function">isSolution</a> <a id="6186" class="Symbol">:</a> <a id="6188" class="Symbol">(∀</a> <a id="6191" href="Complexity.CSP.html#6191" class="Bound">v</a> <a id="6193" class="Symbol">→</a> <a id="6195" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6203" class="Symbol">(</a><a id="6204" href="Algebras.Setoid.Basic.html#3179" class="Field">Domain</a> <a id="6211" class="Symbol">(</a><a id="6212" href="Complexity.CSP.html#5984" class="Bound">𝒜</a> <a id="6214" href="Complexity.CSP.html#6191" class="Bound">v</a><a id="6215" class="Symbol">)))</a> <a id="6219" class="Symbol">→</a> <a id="6221" href="Complexity.CSP.html#3387" class="Primitive">Type</a> <a id="6226" class="Symbol">_</a>  <a id="6229" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6270" href="Complexity.CSP.html#6175" class="Function">isSolution</a> <a id="6281" href="Complexity.CSP.html#6281" class="Bound">f</a> <a id="6283" class="Symbol">=</a> <a id="6285" class="Symbol">∀</a> <a id="6287" href="Complexity.CSP.html#6287" class="Bound">i</a> <a id="6289" class="Symbol">→</a> <a id="6291" class="Symbol">(</a><a id="6292" href="Complexity.CSP.html#4884" class="Function">Constraint.satisfies</a> <a id="6313" class="Symbol">(</a><a id="6314" href="Complexity.CSP.html#6120" class="Field">cs</a> <a id="6317" href="Complexity.CSP.html#6287" class="Bound">i</a><a id="6318" class="Symbol">))</a> <a id="6321" href="Complexity.CSP.html#6281" class="Bound">f</a>  <a id="6324" class="Comment">-- if it satisfies all the constraints.</a>

</pre>



--------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


