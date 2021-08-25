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

<a id="3419" class="Keyword">open</a> <a id="3424" class="Keyword">import</a> <a id="3431" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="3446" class="Keyword">using</a> <a id="3452" class="Symbol">(</a> <a id="3454" href="Algebras.Basic.html#1140" class="Generalizable">𝓞</a> <a id="3456" class="Symbol">;</a> <a id="3458" href="Algebras.Basic.html#1142" class="Generalizable">𝓥</a> <a id="3460" class="Symbol">;</a> <a id="3462" href="Algebras.Basic.html#3566" class="Function">Signature</a> <a id="3472" class="Symbol">)</a>

<a id="3475" class="Keyword">module</a> <a id="3482" href="Complexity.CSP.html" class="Module">Complexity.CSP</a> <a id="3497" class="Symbol">{</a><a id="3498" href="Complexity.CSP.html#3498" class="Bound">𝑆</a> <a id="3500" class="Symbol">:</a> <a id="3502" href="Algebras.Basic.html#3566" class="Function">Signature</a> <a id="3512" href="Algebras.Basic.html#1140" class="Generalizable">𝓞</a> <a id="3514" href="Algebras.Basic.html#1142" class="Generalizable">𝓥</a><a id="3515" class="Symbol">}</a> <a id="3517" class="Keyword">where</a>

<a id="3524" class="Comment">-- Imports from Agda and the Agda Standard Library ------------------------------</a>
<a id="3606" class="Keyword">open</a> <a id="3611" class="Keyword">import</a> <a id="3618" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>   <a id="3635" class="Keyword">using</a> <a id="3641" class="Symbol">(</a> <a id="3643" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="3647" class="Symbol">;</a> <a id="3649" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="3654" class="Symbol">;</a> <a id="3656" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3661" class="Symbol">)</a> <a id="3663" class="Keyword">renaming</a> <a id="3672" class="Symbol">(</a> <a id="3674" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="3678" class="Symbol">to</a> <a id="3681" class="Primitive">Type</a> <a id="3686" class="Symbol">)</a>
<a id="3688" class="Keyword">open</a> <a id="3693" class="Keyword">import</a> <a id="3700" href="Function.Base.html" class="Module">Function.Base</a>    <a id="3717" class="Keyword">using</a> <a id="3723" class="Symbol">(</a> <a id="3725" href="Function.Base.html#1031" class="Function Operator">_∘_</a> <a id="3729" class="Symbol">)</a>
<a id="3731" class="Keyword">open</a> <a id="3736" class="Keyword">import</a> <a id="3743" href="Relation.Binary.html" class="Module">Relation.Binary</a>  <a id="3760" class="Keyword">using</a> <a id="3766" class="Symbol">(</a> <a id="3768" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="3775" class="Symbol">)</a>

<a id="3778" class="Comment">-- Imports from the Agda Universal Algebra Library ------------------------------</a>
<a id="3860" class="Keyword">open</a> <a id="3865" class="Keyword">import</a> <a id="3872" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>    <a id="3896" class="Keyword">using</a> <a id="3902" class="Symbol">(</a> <a id="3904" href="Relations.Continuous.html#4356" class="Function">ΠΡ</a> <a id="3907" class="Symbol">;</a> <a id="3909" href="Relations.Continuous.html#4464" class="Function">ΠΡ-syntax</a> <a id="3919" class="Symbol">)</a>
<a id="3921" class="Keyword">open</a> <a id="3926" class="Keyword">import</a> <a id="3933" href="Algebras.Setoid.Basic.html" class="Module">Algebras.Setoid.Basic</a> <a id="3955" class="Symbol">{</a><a id="3956" class="Argument">𝑆</a> <a id="3958" class="Symbol">=</a> <a id="3960" href="Complexity.CSP.html#3498" class="Bound">𝑆</a><a id="3961" class="Symbol">}</a> <a id="3963" class="Keyword">using</a> <a id="3969" class="Symbol">(</a> <a id="3971" href="Algebras.Setoid.Basic.html#3240" class="Record">SetoidAlgebra</a> <a id="3985" class="Symbol">)</a>

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

<a id="4714" class="Keyword">module</a> <a id="4721" href="Complexity.CSP.html#4721" class="Module">_</a> <a id="4723" class="Comment">-- levels for...</a>
         <a id="4749" class="Symbol">{</a><a id="4750" href="Complexity.CSP.html#4750" class="Bound">ι</a> <a id="4752" class="Symbol">:</a> <a id="4754" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4759" class="Symbol">}</a> <a id="4761" class="Comment">-- ...arity (or argument index) types</a>
         <a id="4808" class="Symbol">{</a><a id="4809" href="Complexity.CSP.html#4809" class="Bound">ν</a> <a id="4811" class="Symbol">:</a> <a id="4813" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4818" class="Symbol">}</a> <a id="4820" class="Comment">-- ...variable symbol types</a>
         <a id="4857" class="Symbol">{</a><a id="4858" href="Complexity.CSP.html#4858" class="Bound">α</a> <a id="4860" href="Complexity.CSP.html#4860" class="Bound">ℓ</a> <a id="4862" class="Symbol">:</a> <a id="4864" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="4869" class="Symbol">}</a> <a id="4871" class="Comment">-- ... domain types</a>
         <a id="4900" class="Keyword">where</a>
 <a id="4907" class="Keyword">open</a> <a id="4912" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="4920" class="Keyword">record</a> <a id="4927" href="Complexity.CSP.html#4927" class="Record">Constraint</a> <a id="4938" class="Symbol">(</a><a id="4939" href="Complexity.CSP.html#4939" class="Bound">var</a> <a id="4943" class="Symbol">:</a> <a id="4945" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="4950" href="Complexity.CSP.html#4809" class="Bound">ν</a><a id="4951" class="Symbol">)</a> <a id="4953" class="Symbol">(</a><a id="4954" href="Complexity.CSP.html#4954" class="Bound">dom</a> <a id="4958" class="Symbol">:</a> <a id="4960" href="Complexity.CSP.html#4939" class="Bound">var</a> <a id="4964" class="Symbol">→</a> <a id="4966" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="4973" href="Complexity.CSP.html#4858" class="Bound">α</a> <a id="4975" href="Complexity.CSP.html#4860" class="Bound">ℓ</a><a id="4976" class="Symbol">)</a> <a id="4978" class="Symbol">:</a> <a id="4980" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="4985" class="Symbol">(</a><a id="4986" href="Complexity.CSP.html#4809" class="Bound">ν</a> <a id="4988" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4990" href="Complexity.CSP.html#4858" class="Bound">α</a> <a id="4992" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="4994" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="4999" href="Complexity.CSP.html#4750" class="Bound">ι</a><a id="5000" class="Symbol">)</a> <a id="5002" class="Keyword">where</a>
  <a id="5010" class="Keyword">field</a>
   <a id="5019" href="Complexity.CSP.html#5019" class="Field">arity</a>  <a id="5026" class="Symbol">:</a> <a id="5028" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="5033" href="Complexity.CSP.html#4750" class="Bound">ι</a>               <a id="5049" class="Comment">-- The &quot;number&quot; of variables involved in the constraint.</a>
   <a id="5109" href="Complexity.CSP.html#5109" class="Field">scope</a>  <a id="5116" class="Symbol">:</a> <a id="5118" href="Complexity.CSP.html#5019" class="Field">arity</a> <a id="5124" class="Symbol">→</a> <a id="5126" href="Complexity.CSP.html#4939" class="Bound">var</a>          <a id="5139" class="Comment">-- Which variables are involved in the constraint.</a>
   <a id="5193" href="Complexity.CSP.html#5193" class="Field">rel</a>    <a id="5200" class="Symbol">:</a> <a id="5202" href="Relations.Continuous.html#4464" class="Function">ΠΡ[</a> <a id="5206" href="Complexity.CSP.html#5206" class="Bound">i</a> <a id="5208" href="Relations.Continuous.html#4464" class="Function">∈</a> <a id="5210" href="Complexity.CSP.html#5019" class="Field">arity</a> <a id="5216" href="Relations.Continuous.html#4464" class="Function">]</a> <a id="5218" class="Symbol">(</a><a id="5219" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5227" class="Symbol">(</a><a id="5228" href="Complexity.CSP.html#4954" class="Bound">dom</a> <a id="5232" class="Symbol">(</a><a id="5233" href="Complexity.CSP.html#5109" class="Field">scope</a> <a id="5239" href="Complexity.CSP.html#5206" class="Bound">i</a><a id="5240" class="Symbol">)))</a>     <a id="5248" class="Comment">-- The constraint relation.</a>

  <a id="5279" href="Complexity.CSP.html#5279" class="Function">satisfies</a> <a id="5289" class="Symbol">:</a> <a id="5291" class="Symbol">(∀</a> <a id="5294" href="Complexity.CSP.html#5294" class="Bound">v</a> <a id="5296" class="Symbol">→</a> <a id="5298" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="5306" class="Symbol">(</a><a id="5307" href="Complexity.CSP.html#4954" class="Bound">dom</a> <a id="5311" href="Complexity.CSP.html#5294" class="Bound">v</a><a id="5312" class="Symbol">))</a> <a id="5315" class="Symbol">→</a> <a id="5317" href="Complexity.CSP.html#3681" class="Primitive">Type</a>  <a id="5323" class="Comment">-- An assignment 𝑓 : var → dom of values to variables</a>
  <a id="5379" href="Complexity.CSP.html#5279" class="Function">satisfies</a> <a id="5389" href="Complexity.CSP.html#5389" class="Bound">f</a> <a id="5391" class="Symbol">=</a> <a id="5393" href="Complexity.CSP.html#5193" class="Field">rel</a> <a id="5397" class="Symbol">(</a><a id="5398" href="Complexity.CSP.html#5389" class="Bound">f</a> <a id="5400" href="Function.Base.html#1031" class="Function Operator">∘</a> <a id="5402" href="Complexity.CSP.html#5109" class="Field">scope</a><a id="5407" class="Symbol">)</a>      <a id="5414" class="Comment">-- *satisfies* the constraint 𝐶 = (σ , 𝑅) provided</a>
                                    <a id="5501" class="Comment">-- 𝑓 ∘ σ ∈ 𝑅, where σ is the scope of the constraint.</a>
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

 <a id="6354" class="Keyword">open</a> <a id="6359" href="Algebras.Setoid.Basic.html#3240" class="Module">SetoidAlgebra</a>
 <a id="6374" class="Keyword">open</a> <a id="6379" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a>
 <a id="6387" class="Keyword">record</a> <a id="6394" href="Complexity.CSP.html#6394" class="Record">CSPInstance</a> <a id="6406" class="Symbol">(</a><a id="6407" href="Complexity.CSP.html#6407" class="Bound">var</a> <a id="6411" class="Symbol">:</a> <a id="6413" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="6418" href="Complexity.CSP.html#4809" class="Bound">ν</a><a id="6419" class="Symbol">)(</a><a id="6421" href="Complexity.CSP.html#6421" class="Bound">𝒜</a> <a id="6423" class="Symbol">:</a> <a id="6425" href="Complexity.CSP.html#6407" class="Bound">var</a> <a id="6429" class="Symbol">→</a> <a id="6431" href="Algebras.Setoid.Basic.html#3240" class="Record">SetoidAlgebra</a> <a id="6445" href="Complexity.CSP.html#4858" class="Bound">α</a> <a id="6447" href="Complexity.CSP.html#4860" class="Bound">ℓ</a><a id="6448" class="Symbol">)</a> <a id="6450" class="Symbol">:</a> <a id="6452" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="6457" class="Symbol">(</a><a id="6458" href="Complexity.CSP.html#4809" class="Bound">ν</a> <a id="6460" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6462" href="Complexity.CSP.html#4858" class="Bound">α</a> <a id="6464" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="6466" href="Agda.Primitive.html#780" class="Primitive">lsuc</a> <a id="6471" href="Complexity.CSP.html#4750" class="Bound">ι</a><a id="6472" class="Symbol">)</a> <a id="6474" class="Keyword">where</a>
  <a id="6482" class="Keyword">field</a>
   <a id="6491" href="Complexity.CSP.html#6491" class="Field">ar</a> <a id="6494" class="Symbol">:</a> <a id="6496" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="6501" href="Complexity.CSP.html#4750" class="Bound">ι</a>       <a id="6509" class="Comment">-- ar indexes the contraints in the instance</a>
   <a id="6557" href="Complexity.CSP.html#6557" class="Field">cs</a> <a id="6560" class="Symbol">:</a> <a id="6562" class="Symbol">(</a><a id="6563" href="Complexity.CSP.html#6563" class="Bound">i</a> <a id="6565" class="Symbol">:</a> <a id="6567" href="Complexity.CSP.html#6491" class="Field">ar</a><a id="6569" class="Symbol">)</a> <a id="6571" class="Symbol">→</a> <a id="6573" href="Complexity.CSP.html#4927" class="Record">Constraint</a> <a id="6584" href="Complexity.CSP.html#6407" class="Bound">var</a> <a id="6588" class="Symbol">(λ</a> <a id="6591" href="Complexity.CSP.html#6591" class="Bound">v</a> <a id="6593" class="Symbol">→</a> <a id="6595" href="Algebras.Setoid.Basic.html#3306" class="Field">Domain</a> <a id="6602" class="Symbol">(</a><a id="6603" href="Complexity.CSP.html#6421" class="Bound">𝒜</a> <a id="6605" href="Complexity.CSP.html#6591" class="Bound">v</a><a id="6606" class="Symbol">))</a>

  <a id="6612" href="Complexity.CSP.html#6612" class="Function">isSolution</a> <a id="6623" class="Symbol">:</a> <a id="6625" class="Symbol">(∀</a> <a id="6628" href="Complexity.CSP.html#6628" class="Bound">v</a> <a id="6630" class="Symbol">→</a> <a id="6632" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="6640" class="Symbol">(</a><a id="6641" href="Algebras.Setoid.Basic.html#3306" class="Field">Domain</a> <a id="6648" class="Symbol">(</a><a id="6649" href="Complexity.CSP.html#6421" class="Bound">𝒜</a> <a id="6651" href="Complexity.CSP.html#6628" class="Bound">v</a><a id="6652" class="Symbol">)))</a> <a id="6656" class="Symbol">→</a> <a id="6658" href="Complexity.CSP.html#3681" class="Primitive">Type</a> <a id="6663" class="Symbol">_</a>  <a id="6666" class="Comment">-- An assignment *solves* the instance</a>
  <a id="6707" href="Complexity.CSP.html#6612" class="Function">isSolution</a> <a id="6718" href="Complexity.CSP.html#6718" class="Bound">f</a> <a id="6720" class="Symbol">=</a> <a id="6722" class="Symbol">∀</a> <a id="6724" href="Complexity.CSP.html#6724" class="Bound">i</a> <a id="6726" class="Symbol">→</a> <a id="6728" class="Symbol">(</a><a id="6729" href="Complexity.CSP.html#5279" class="Function">Constraint.satisfies</a> <a id="6750" class="Symbol">(</a><a id="6751" href="Complexity.CSP.html#6557" class="Field">cs</a> <a id="6754" href="Complexity.CSP.html#6724" class="Bound">i</a><a id="6755" class="Symbol">))</a> <a id="6758" href="Complexity.CSP.html#6718" class="Bound">f</a>  <a id="6761" class="Comment">-- if it satisfies all the constraints.</a>

</pre>


--------------------------------

<span>[← Complexity.Basic](Complexity.Basic.html)</span>
<span style="float:right;">[agda-algebras ↑](agda-algebras.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


