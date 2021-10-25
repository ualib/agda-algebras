---
layout: default
title : "Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team and Libor Barto"
---

All excercises in this module were created by Libor Barto for students at Charles University in Prague. They were formalized in dependent type theory by the [agda-algebras development team][].

### CSP Exercises

<pre class="Agda">

<a id="415" class="Symbol">{-#</a> <a id="419" class="Keyword">OPTIONS</a> <a id="427" class="Pragma">--without-K</a> <a id="439" class="Pragma">--exact-split</a> <a id="453" class="Pragma">--safe</a> <a id="460" class="Symbol">#-}</a>

<a id="465" class="Keyword">module</a> <a id="472" href="Exercises.Complexity.FiniteCSP.html" class="Module">Exercises.Complexity.FiniteCSP</a>  <a id="504" class="Keyword">where</a>

<a id="511" class="Keyword">open</a> <a id="516" class="Keyword">import</a> <a id="523" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="539" class="Keyword">using</a> <a id="545" class="Symbol">(</a> <a id="547" class="Symbol">)</a> <a id="549" class="Keyword">renaming</a> <a id="558" class="Symbol">(</a><a id="559" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="565" class="Symbol">to</a> <a id="568" class="Primitive">ℓ₀</a> <a id="571" class="Symbol">)</a>
<a id="573" class="Keyword">open</a> <a id="578" class="Keyword">import</a> <a id="585" href="Data.Product.html" class="Module">Data.Product</a>    <a id="601" class="Keyword">using</a> <a id="607" class="Symbol">(</a> <a id="609" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="613" class="Symbol">;</a> <a id="615" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="619" class="Symbol">)</a>
<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="Data.Unit.Base.html" class="Module">Data.Unit.Base</a>  <a id="649" class="Keyword">using</a> <a id="655" class="Symbol">()</a> <a id="658" class="Keyword">renaming</a> <a id="667" class="Symbol">(</a> <a id="669" href="Agda.Builtin.Unit.html#201" class="InductiveConstructor">tt</a> <a id="672" class="Symbol">to</a> <a id="675" class="InductiveConstructor">𝟎</a> <a id="677" class="Symbol">)</a>
<a id="679" class="Keyword">open</a> <a id="684" class="Keyword">import</a> <a id="691" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="707" class="Keyword">using</a> <a id="713" class="Symbol">(</a> <a id="715" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="720" class="Symbol">;</a> <a id="722" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="726" class="Symbol">)</a>

<a id="729" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="822" class="Keyword">open</a> <a id="827" class="Keyword">import</a> <a id="834" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>         <a id="865" class="Keyword">using</a> <a id="871" class="Symbol">(</a> <a id="873" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="875" class="Symbol">;</a> <a id="877" href="Overture.Preliminaries.html#3843" class="Datatype">𝟛</a> <a id="879" class="Symbol">)</a>
<a id="881" class="Keyword">open</a> <a id="886" class="Keyword">import</a> <a id="893" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>           <a id="924" class="Keyword">using</a> <a id="930" class="Symbol">(</a> <a id="932" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="936" class="Symbol">)</a>
<a id="938" class="Keyword">open</a> <a id="943" class="Keyword">import</a> <a id="950" href="Structures.Basic.html" class="Module">Structures.Basic</a>               <a id="981" class="Keyword">using</a> <a id="987" class="Symbol">(</a> <a id="989" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="999" class="Symbol">;</a> <a id="1001" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="1011" class="Symbol">)</a>
<a id="1013" class="Keyword">open</a> <a id="1018" class="Keyword">import</a> <a id="1025" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="1056" class="Keyword">using</a> <a id="1062" class="Symbol">(</a> <a id="1064" href="Examples.Structures.Signatures.html#700" class="Function">S∅</a> <a id="1067" class="Symbol">;</a> <a id="1069" href="Examples.Structures.Signatures.html#1028" class="Function">S001</a> <a id="1074" class="Symbol">;</a> <a id="1076" href="Examples.Structures.Signatures.html#1283" class="Function">S021</a><a id="1080" class="Symbol">)</a>
<a id="1082" class="Keyword">open</a> <a id="1087" class="Keyword">import</a> <a id="1094" href="Structures.Homs.html" class="Module">Structures.Homs</a>                <a id="1125" class="Keyword">using</a> <a id="1131" class="Symbol">(</a> <a id="1133" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="1137" class="Symbol">)</a>
<a id="1139" class="Keyword">open</a> <a id="1144" href="Structures.Basic.html#1234" class="Module">signature</a>
<a id="1154" class="Keyword">open</a> <a id="1159" href="Structures.Basic.html#1568" class="Module">structure</a>

</pre>

Some exercises below refer to the following relations on 𝟚 := \{0, 1\} (where i, j ∈ 𝟚):

\begin{align*}
 Cᵃᵢ    & := \{ i \}                             \\
 Rᵃ    & := \{ (0, 0), (1, 1) \}                 \\
 Nᵃ    & := \{ (0, 1), (1, 0) \}                  \\
 Sᵃ_{ij}  & := 𝟚² - \{ (i , j) \},                    \\
 Hᵃ    & := 𝟚³ - \{ (1, 1, 0) \}                 \\
 Gᵃ₁   & := \{ (0,0,0), (0,1,1), (1,0,1), (1,1,0) \} \\
 Gᵃ₂   & := \{ (0,0,1), (0,1,0), (1,0,0), (1,1,1) \}
\end{align*}


**Exercise 1**. Prove that the definitions of CSP(𝔸) (satisfiability of a list of constraints, homomorphism   problem, truth of primitive positive formulas) are equivalent.


**Exercise 2**. Find a polymomial-time algorithm for CSP(A), where

2.1. 𝑨 = ({0, 1}, Rᵃ) = (𝟚 , \{(0,0), (1, 1)\})
2.2. 𝑨 = ({0, 1}, Rᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ 0 \} , \{ 1 \})
2.3. 𝑨 = ({0, 1}, S₁₀ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \})
2.4. 𝑨 = ({0, 1}, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.5. 𝑨 = ({0, 1}, S₀₁ᵃ, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})
2.6. 𝑨 = ({0, 1}, Nᵃ) = (𝟚 , \{ (0, 1) , (1, 0) \})
2.7. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})
2.8. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ, 𝑆₀₀, S₀₁ᵃ, S₁₀ᵃ, S₁₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})
2.9. 𝑨 = ({0, 1}, all unary and binary relations)



**Solution 2.1**. If 𝑨 = ({0, 1}, Rᵃ) = (𝟚 , \{(0,0), (1, 1)\}), then an instance of (the HOM
formulation of) CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ⟩, where Rᵇ ⊆ B² and we must decide
whether there exists a homomorphism f : 𝑩 → 𝑨, that is, a map f : B → A (= 𝟚) such that
∀ (b, b'), if (b, b') ∈ Rᵇ, then (f b, f b') ∈ Rᵇ.

Of course, the constant map f ≡ 0 that sends every element of B to 0 (as well as the
constantly-1 map) is such a homomorphism.  Let's prove this formally.

<pre class="Agda">
<a id="3209" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3216" href="Exercises.Complexity.FiniteCSP.html#3216" class="Module">solution-2-1</a> <a id="3229" class="Keyword">where</a>

 <a id="3237" class="Comment">-- The (purely) relational structure with</a>
 <a id="3280" class="Comment">-- + 2-element domain,</a>
 <a id="3304" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3355" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3360" href="Exercises.Complexity.FiniteCSP.html#3360" class="Datatype">Rᵃ</a> <a id="3363" class="Symbol">:</a> <a id="3365" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3370" class="Symbol">(</a><a id="3371" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="3373" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3375" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a><a id="3376" class="Symbol">)</a> <a id="3378" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="3381" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3389" href="Exercises.Complexity.FiniteCSP.html#3389" class="InductiveConstructor">r1</a> <a id="3392" class="Symbol">:</a> <a id="3394" class="Symbol">(</a><a id="3395" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a> <a id="3399" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3401" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a> <a id="3405" class="Symbol">)</a> <a id="3407" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3409" href="Exercises.Complexity.FiniteCSP.html#3360" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3414" href="Exercises.Complexity.FiniteCSP.html#3414" class="InductiveConstructor">r2</a> <a id="3417" class="Symbol">:</a> <a id="3419" class="Symbol">(</a><a id="3420" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a> <a id="3424" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3426" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a> <a id="3430" class="Symbol">)</a> <a id="3432" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3434" href="Exercises.Complexity.FiniteCSP.html#3360" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3439" href="Exercises.Complexity.FiniteCSP.html#3439" class="Function">𝑨</a> <a id="3441" class="Symbol">:</a> <a id="3443" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3453" href="Examples.Structures.Signatures.html#700" class="Function">S∅</a>    <a id="3459" class="Comment">-- (no operation symbols)</a>
               <a id="3500" href="Examples.Structures.Signatures.html#1028" class="Function">S001</a>  <a id="3506" class="Comment">-- (one binary relation symbol)</a>

 <a id="3540" href="Exercises.Complexity.FiniteCSP.html#3439" class="Function">𝑨</a> <a id="3542" class="Symbol">=</a> <a id="3544" class="Keyword">record</a> <a id="3551" class="Symbol">{</a> <a id="3553" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="3561" class="Symbol">=</a> <a id="3563" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a>
            <a id="3577" class="Symbol">;</a> <a id="3579" href="Structures.Basic.html#1739" class="Field">op</a> <a id="3582" class="Symbol">=</a> <a id="3584" class="Symbol">λ</a> <a id="3586" class="Symbol">()</a>
            <a id="3601" class="Symbol">;</a> <a id="3603" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="3607" class="Symbol">=</a> <a id="3609" class="Symbol">λ</a> <a id="3611" href="Exercises.Complexity.FiniteCSP.html#3611" class="Bound">_</a> <a id="3613" href="Exercises.Complexity.FiniteCSP.html#3613" class="Bound">x</a> <a id="3615" class="Symbol">→</a> <a id="3617" class="Symbol">((</a><a id="3619" href="Exercises.Complexity.FiniteCSP.html#3613" class="Bound">x</a> <a id="3621" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a><a id="3624" class="Symbol">)</a> <a id="3626" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3628" class="Symbol">(</a><a id="3629" href="Exercises.Complexity.FiniteCSP.html#3613" class="Bound">x</a> <a id="3631" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a><a id="3634" class="Symbol">))</a> <a id="3637" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3639" href="Exercises.Complexity.FiniteCSP.html#3360" class="Datatype">Rᵃ</a>
            <a id="3654" class="Symbol">}</a>


 <a id="3659" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3767" href="Exercises.Complexity.FiniteCSP.html#3767" class="Function">claim</a> <a id="3773" class="Symbol">:</a> <a id="3775" class="Symbol">(</a><a id="3776" href="Exercises.Complexity.FiniteCSP.html#3776" class="Bound">𝑩</a> <a id="3778" class="Symbol">:</a> <a id="3780" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3790" class="Symbol">{</a><a id="3791" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3793" class="Symbol">}{</a><a id="3795" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3797" class="Symbol">}{</a><a id="3799" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3801" class="Symbol">}{</a><a id="3803" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3805" class="Symbol">}</a> <a id="3807" href="Examples.Structures.Signatures.html#700" class="Function">S∅</a> <a id="3810" href="Examples.Structures.Signatures.html#1028" class="Function">S001</a> <a id="3815" class="Symbol">{</a><a id="3816" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3818" class="Symbol">}{</a><a id="3820" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3822" class="Symbol">})</a> <a id="3825" class="Symbol">→</a> <a id="3827" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="3831" href="Exercises.Complexity.FiniteCSP.html#3776" class="Bound">𝑩</a> <a id="3833" href="Exercises.Complexity.FiniteCSP.html#3439" class="Function">𝑨</a>
 <a id="3836" href="Exercises.Complexity.FiniteCSP.html#3767" class="Function">claim</a> <a id="3842" href="Exercises.Complexity.FiniteCSP.html#3842" class="Bound">𝑩</a> <a id="3844" class="Symbol">=</a> <a id="3846" class="Symbol">(λ</a> <a id="3849" href="Exercises.Complexity.FiniteCSP.html#3849" class="Bound">x</a> <a id="3851" class="Symbol">→</a> <a id="3853" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a><a id="3856" class="Symbol">)</a> <a id="3858" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3860" class="Symbol">(λ</a> <a id="3863" href="Exercises.Complexity.FiniteCSP.html#3863" class="Bound">_</a> <a id="3865" href="Exercises.Complexity.FiniteCSP.html#3865" class="Bound">_</a> <a id="3867" href="Exercises.Complexity.FiniteCSP.html#3867" class="Bound">_</a> <a id="3869" class="Symbol">→</a> <a id="3871" href="Exercises.Complexity.FiniteCSP.html#3389" class="InductiveConstructor">r1</a><a id="3873" class="Symbol">)</a> <a id="3875" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3877" class="Symbol">λ</a> <a id="3879" class="Symbol">()</a>

</pre>

In general, whenever the template structure 𝑨 has a one-element subuniverse, say, \{ a \},
then the constant map that always gives a is a homomorphism from any structure in the given
signature to 𝑨. ∎



**Solution 2.2**. If 𝑨 = (\{ 0, 1 \}, Rᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0, 0) , (1, 1) \} , \{ 0 \} , \{ 1 \}),
then an instance of HOM CSP(𝑨) is a relational structure 𝑩 = (B, Rᵇ, C₀ᵇ, C₁ᵇ), where
Rᵇ ⊆ B², C₀ᵇ ⊆ B, C₁ᵇ ⊆ B, and we must decide whether there exists a homomorphism
f : hom 𝑩 𝑨, that is, a map f : B → 𝟚 such that the following conditions hold:
 1. ∀ (x, y) ∈ B², (x, y) ∈ Rᵇ implies (f x , f y) ∈ Rᵇ,
 2. f is constantly 0 on C₀ᵇ, and
 3. f is constantly 1 on C₁ᵇ.

The first condition says that if (x, y) ∈ Rᵇ, then either f x = 0 = f y or f x = 1 = f y.

Therefore, there exists a homomorphism f : hom 𝑩 𝑨 iff Rᵇ ∩ C₀ᵇ × C₁ᵇ = ∅ = Rᵇ ∩ C₁ᵇ × C₀ᵇ.

We can check this in polynomial time (in the size of the input instance 𝑩) since we just need
to check each pair (x, y) ∈ Rᵇ and make sure that the following two implications hold:

 1.  x ∈ C₀ᵇ  only if  y ∉ C₁ᵇ, and
 2.  x ∈ C₁ᵇ  only if  y ∉ C₀ᵇ.

<pre class="Agda">

<a id="5020" class="Keyword">module</a> <a id="solution-2-2"></a><a id="5027" href="Exercises.Complexity.FiniteCSP.html#5027" class="Module">solution-2-2</a> <a id="5040" class="Keyword">where</a>

 <a id="5048" class="Comment">-- The (purely) relational structure with</a>
 <a id="5091" class="Comment">-- + 2-element domain,</a>
 <a id="5115" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5166" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5222" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5227" href="Exercises.Complexity.FiniteCSP.html#5227" class="Datatype">Rᵃ</a> <a id="5230" class="Symbol">:</a> <a id="5232" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5237" class="Symbol">(</a><a id="5238" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="5240" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5242" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a><a id="5243" class="Symbol">)</a> <a id="5245" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5248" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5256" href="Exercises.Complexity.FiniteCSP.html#5256" class="InductiveConstructor">r1</a> <a id="5259" class="Symbol">:</a> <a id="5261" class="Symbol">(</a><a id="5262" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a> <a id="5266" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5268" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a> <a id="5272" class="Symbol">)</a> <a id="5274" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5276" href="Exercises.Complexity.FiniteCSP.html#5227" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5281" href="Exercises.Complexity.FiniteCSP.html#5281" class="InductiveConstructor">r2</a> <a id="5284" class="Symbol">:</a> <a id="5286" class="Symbol">(</a><a id="5287" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a> <a id="5291" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5293" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a> <a id="5297" class="Symbol">)</a> <a id="5299" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5301" href="Exercises.Complexity.FiniteCSP.html#5227" class="Datatype">Rᵃ</a>

 <a id="5306" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5311" href="Exercises.Complexity.FiniteCSP.html#5311" class="Datatype">C₀ᵃ</a> <a id="5315" class="Symbol">:</a> <a id="5317" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5322" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="5324" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5327" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5335" href="Exercises.Complexity.FiniteCSP.html#5335" class="InductiveConstructor">c₀</a> <a id="5338" class="Symbol">:</a> <a id="5340" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a> <a id="5344" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5346" href="Exercises.Complexity.FiniteCSP.html#5311" class="Datatype">C₀ᵃ</a>

 <a id="5352" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5357" href="Exercises.Complexity.FiniteCSP.html#5357" class="Datatype">C₁ᵃ</a> <a id="5361" class="Symbol">:</a> <a id="5363" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5368" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="5370" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5373" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5381" href="Exercises.Complexity.FiniteCSP.html#5381" class="InductiveConstructor">c₁</a> <a id="5384" class="Symbol">:</a> <a id="5386" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a> <a id="5390" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5392" href="Exercises.Complexity.FiniteCSP.html#5357" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5399" href="Exercises.Complexity.FiniteCSP.html#5399" class="Function">𝑨</a> <a id="5401" class="Symbol">:</a> <a id="5403" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="5413" href="Examples.Structures.Signatures.html#700" class="Function">S∅</a>    <a id="5419" class="Comment">-- (no operations)</a>
               <a id="5453" href="Examples.Structures.Signatures.html#1283" class="Function">S021</a>  <a id="5459" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5510" href="Exercises.Complexity.FiniteCSP.html#5399" class="Function">𝑨</a> <a id="5512" class="Symbol">=</a> <a id="5514" class="Keyword">record</a> <a id="5521" class="Symbol">{</a> <a id="5523" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="5531" class="Symbol">=</a> <a id="5533" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a>
            <a id="5547" class="Symbol">;</a> <a id="5549" href="Structures.Basic.html#1739" class="Field">op</a> <a id="5552" class="Symbol">=</a> <a id="5554" class="Symbol">λ</a> <a id="5556" class="Symbol">()</a>
            <a id="5571" class="Symbol">;</a> <a id="5573" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="5577" class="Symbol">=</a> <a id="5579" href="Exercises.Complexity.FiniteCSP.html#5628" class="Function">rels</a>
            <a id="5596" class="Symbol">}</a>
            <a id="5610" class="Keyword">where</a>
            <a id="5628" href="Exercises.Complexity.FiniteCSP.html#5628" class="Function">rels</a> <a id="5633" class="Symbol">:</a> <a id="5635" class="Symbol">(</a><a id="5636" href="Exercises.Complexity.FiniteCSP.html#5636" class="Bound">r</a> <a id="5638" class="Symbol">:</a> <a id="5640" href="Overture.Preliminaries.html#3843" class="Datatype">𝟛</a><a id="5641" class="Symbol">)</a> <a id="5643" class="Symbol">→</a> <a id="5645" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="5649" href="Overture.Preliminaries.html#3746" class="Datatype">𝟚</a> <a id="5651" class="Symbol">(</a><a id="5652" href="Structures.Basic.html#1313" class="Field">arity</a> <a id="5658" href="Examples.Structures.Signatures.html#1283" class="Function">S021</a> <a id="5663" href="Exercises.Complexity.FiniteCSP.html#5636" class="Bound">r</a><a id="5664" class="Symbol">)</a>
            <a id="5678" href="Exercises.Complexity.FiniteCSP.html#5628" class="Function">rels</a> <a id="5683" href="Overture.Preliminaries.html#3862" class="InductiveConstructor">𝟛.𝟎</a> <a id="5687" href="Exercises.Complexity.FiniteCSP.html#5687" class="Bound">x</a> <a id="5689" class="Symbol">=</a> <a id="5691" class="Symbol">((</a><a id="5693" href="Exercises.Complexity.FiniteCSP.html#5687" class="Bound">x</a> <a id="5695" href="Overture.Preliminaries.html#3796" class="InductiveConstructor">𝟚.𝟎</a><a id="5698" class="Symbol">)</a> <a id="5700" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5702" class="Symbol">(</a><a id="5703" href="Exercises.Complexity.FiniteCSP.html#5687" class="Bound">x</a> <a id="5705" href="Overture.Preliminaries.html#3805" class="InductiveConstructor">𝟚.𝟏</a><a id="5708" class="Symbol">))</a> <a id="5711" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5713" href="Exercises.Complexity.FiniteCSP.html#5227" class="Datatype">Rᵃ</a>
            <a id="5728" href="Exercises.Complexity.FiniteCSP.html#5628" class="Function">rels</a> <a id="5733" href="Overture.Preliminaries.html#3871" class="InductiveConstructor">𝟛.𝟏</a> <a id="5737" href="Exercises.Complexity.FiniteCSP.html#5737" class="Bound">x</a> <a id="5739" class="Symbol">=</a> <a id="5741" href="Exercises.Complexity.FiniteCSP.html#5737" class="Bound">x</a> <a id="5743" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5745" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5747" href="Exercises.Complexity.FiniteCSP.html#5311" class="Datatype">C₀ᵃ</a>
            <a id="5763" href="Exercises.Complexity.FiniteCSP.html#5628" class="Function">rels</a> <a id="5768" href="Overture.Preliminaries.html#3880" class="InductiveConstructor">𝟛.𝟐</a> <a id="5772" href="Exercises.Complexity.FiniteCSP.html#5772" class="Bound">x</a> <a id="5774" class="Symbol">=</a> <a id="5776" href="Exercises.Complexity.FiniteCSP.html#5772" class="Bound">x</a> <a id="5778" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5780" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5782" href="Exercises.Complexity.FiniteCSP.html#5357" class="Datatype">C₁ᵃ</a>


 <a id="5789" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5893" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5939" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5975" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6046" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6124" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6204" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6252" class="Comment">--          )</a>
 <a id="6267" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6288" class="Comment">-- claim 𝑩 x = {!!}</a>

</pre>


(The remainder are "todo.")

**Solution 2.3**. 𝑨 = ({0, 1}, S₁₀ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \})

**Solution 2.4**. 𝑨 = ({0, 1}, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.5**. 𝑨 = ({0, 1}, S₀₁ᵃ, S₁₀ᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.6**. 𝑨 = ({0, 1}, Nᵃ) = (𝟚 , \{ (0, 1) , (1, 0) \})

**Solution 2.7**. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \})

**Solution 2.8**. 𝑨 = ({0, 1}, Rᵃ, Nᵃ, C₀ᵃ, C₁ᵃ, 𝑆₀₀, S₀₁ᵃ, S₁₀ᵃ, S₁₁ᵃ) = (𝟚 , \{ (0,0) , (1, 1) \} , \{ (0, 1) , (1, 0) \} , \{ 0 \} , \{ 1 \} , 𝟚³ - \{ (0, 0) \} , 𝟚³ - \{ (0, 1) \} , 𝟚³ - \{ (1, 0) \} , 𝟚³ - \{ (1, 1) \})

**Solution 2.9**. 𝑨 = ({0, 1}, all unary and binary relations)


**Exercise 3**. Find a polynomial-time algorithm for CSP({0, 1}, Hᵃ, C₀ᵃ, C₁ᵃ).

**Exercise 4**. Find a polynomial-time algorithm for CSP({0, 1}, C₀ᵃ, C₁ᵃ, G₁ᵃ, G₂ᵃ).

**Exercise 5**. Find a polynomial-time algorithm for CSP(ℚ, <).

--------------------------------

{% include UALib.Links.md %}


