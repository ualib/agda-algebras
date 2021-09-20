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
<a id="621" class="Keyword">open</a> <a id="626" class="Keyword">import</a> <a id="633" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="649" class="Keyword">using</a> <a id="655" class="Symbol">(</a> <a id="657" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="662" class="Symbol">;</a> <a id="664" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="668" class="Symbol">)</a>

<a id="671" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="764" class="Keyword">open</a> <a id="769" class="Keyword">import</a> <a id="776" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>         <a id="807" class="Keyword">using</a> <a id="813" class="Symbol">(</a> <a id="815" href="Overture.Preliminaries.html#3617" class="Datatype">𝟘</a> <a id="817" class="Symbol">;</a> <a id="819" href="Overture.Preliminaries.html#3693" class="Datatype">𝟙</a> <a id="821" class="Symbol">;</a> <a id="823" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="825" class="Symbol">;</a> <a id="827" href="Overture.Preliminaries.html#3845" class="Datatype">𝟛</a> <a id="829" class="Symbol">)</a>
<a id="831" class="Keyword">open</a> <a id="836" class="Keyword">import</a> <a id="843" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>           <a id="874" class="Keyword">using</a> <a id="880" class="Symbol">(</a> <a id="882" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="886" class="Symbol">)</a>
<a id="888" class="Keyword">open</a> <a id="893" class="Keyword">import</a> <a id="900" href="Structures.Basic.html" class="Module">Structures.Basic</a>               <a id="931" class="Keyword">using</a> <a id="937" class="Symbol">(</a> <a id="939" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="949" class="Symbol">;</a> <a id="951" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="961" class="Symbol">)</a>
<a id="963" class="Keyword">open</a> <a id="968" class="Keyword">import</a> <a id="975" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="1006" class="Keyword">using</a> <a id="1012" class="Symbol">(</a> <a id="1014" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="1017" class="Symbol">;</a> <a id="1019" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="1024" class="Symbol">;</a> <a id="1026" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a><a id="1030" class="Symbol">)</a>
<a id="1032" class="Keyword">open</a> <a id="1037" class="Keyword">import</a> <a id="1044" href="Structures.Homs.html" class="Module">Structures.Homs</a>                <a id="1075" class="Keyword">using</a> <a id="1081" class="Symbol">(</a> <a id="1083" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="1087" class="Symbol">)</a>
<a id="1089" class="Keyword">open</a> <a id="1094" href="Structures.Basic.html#1234" class="Module">signature</a>
<a id="1104" class="Keyword">open</a> <a id="1109" href="Structures.Basic.html#1568" class="Module">structure</a>

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
<a id="3159" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3166" href="Exercises.Complexity.FiniteCSP.html#3166" class="Module">solution-2-1</a> <a id="3179" class="Keyword">where</a>

 <a id="3187" class="Comment">-- The (purely) relational structure with</a>
 <a id="3230" class="Comment">-- + 2-element domain,</a>
 <a id="3254" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3305" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3310" href="Exercises.Complexity.FiniteCSP.html#3310" class="Datatype">Rᵃ</a> <a id="3313" class="Symbol">:</a> <a id="3315" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3320" class="Symbol">(</a><a id="3321" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="3323" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3325" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a><a id="3326" class="Symbol">)</a> <a id="3328" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="3331" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3339" href="Exercises.Complexity.FiniteCSP.html#3339" class="InductiveConstructor">r1</a> <a id="3342" class="Symbol">:</a> <a id="3344" class="Symbol">(</a><a id="3345" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="3349" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3351" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="3355" class="Symbol">)</a> <a id="3357" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3359" href="Exercises.Complexity.FiniteCSP.html#3310" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3364" href="Exercises.Complexity.FiniteCSP.html#3364" class="InductiveConstructor">r2</a> <a id="3367" class="Symbol">:</a> <a id="3369" class="Symbol">(</a><a id="3370" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="3374" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3376" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="3380" class="Symbol">)</a> <a id="3382" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3384" href="Exercises.Complexity.FiniteCSP.html#3310" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3389" href="Exercises.Complexity.FiniteCSP.html#3389" class="Function">𝑨</a> <a id="3391" class="Symbol">:</a> <a id="3393" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3403" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="3409" class="Comment">-- (no operation symbols)</a>
               <a id="3450" href="Examples.Structures.Signatures.html#893" class="Function">S001</a>  <a id="3456" class="Comment">-- (one binary relation symbol)</a>

 <a id="3490" href="Exercises.Complexity.FiniteCSP.html#3389" class="Function">𝑨</a> <a id="3492" class="Symbol">=</a> <a id="3494" class="Keyword">record</a> <a id="3501" class="Symbol">{</a> <a id="3503" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="3511" class="Symbol">=</a> <a id="3513" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a>
            <a id="3527" class="Symbol">;</a> <a id="3529" href="Structures.Basic.html#1739" class="Field">op</a> <a id="3532" class="Symbol">=</a> <a id="3534" class="Symbol">λ</a> <a id="3536" class="Symbol">()</a>
            <a id="3551" class="Symbol">;</a> <a id="3553" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="3557" class="Symbol">=</a> <a id="3559" class="Symbol">λ</a> <a id="3561" href="Exercises.Complexity.FiniteCSP.html#3561" class="Bound">_</a> <a id="3563" href="Exercises.Complexity.FiniteCSP.html#3563" class="Bound">x</a> <a id="3565" class="Symbol">→</a> <a id="3567" class="Symbol">((</a><a id="3569" href="Exercises.Complexity.FiniteCSP.html#3563" class="Bound">x</a> <a id="3571" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="3574" class="Symbol">)</a> <a id="3576" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3578" class="Symbol">(</a><a id="3579" href="Exercises.Complexity.FiniteCSP.html#3563" class="Bound">x</a> <a id="3581" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a><a id="3584" class="Symbol">))</a> <a id="3587" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3589" href="Exercises.Complexity.FiniteCSP.html#3310" class="Datatype">Rᵃ</a>
            <a id="3604" class="Symbol">}</a>


 <a id="3609" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3717" href="Exercises.Complexity.FiniteCSP.html#3717" class="Function">claim</a> <a id="3723" class="Symbol">:</a> <a id="3725" class="Symbol">(</a><a id="3726" href="Exercises.Complexity.FiniteCSP.html#3726" class="Bound">𝑩</a> <a id="3728" class="Symbol">:</a> <a id="3730" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3740" class="Symbol">{</a><a id="3741" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3743" class="Symbol">}{</a><a id="3745" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3747" class="Symbol">}{</a><a id="3749" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3751" class="Symbol">}{</a><a id="3753" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3755" class="Symbol">}</a> <a id="3757" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="3760" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="3765" class="Symbol">{</a><a id="3766" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3768" class="Symbol">}{</a><a id="3770" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3772" class="Symbol">})</a> <a id="3775" class="Symbol">→</a> <a id="3777" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="3781" href="Exercises.Complexity.FiniteCSP.html#3726" class="Bound">𝑩</a> <a id="3783" href="Exercises.Complexity.FiniteCSP.html#3389" class="Function">𝑨</a>
 <a id="3786" href="Exercises.Complexity.FiniteCSP.html#3717" class="Function">claim</a> <a id="3792" href="Exercises.Complexity.FiniteCSP.html#3792" class="Bound">𝑩</a> <a id="3794" class="Symbol">=</a> <a id="3796" class="Symbol">(λ</a> <a id="3799" href="Exercises.Complexity.FiniteCSP.html#3799" class="Bound">x</a> <a id="3801" class="Symbol">→</a> <a id="3803" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="3806" class="Symbol">)</a> <a id="3808" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3810" class="Symbol">(λ</a> <a id="3813" href="Exercises.Complexity.FiniteCSP.html#3813" class="Bound">_</a> <a id="3815" href="Exercises.Complexity.FiniteCSP.html#3815" class="Bound">_</a> <a id="3817" href="Exercises.Complexity.FiniteCSP.html#3817" class="Bound">_</a> <a id="3819" class="Symbol">→</a> <a id="3821" href="Exercises.Complexity.FiniteCSP.html#3339" class="InductiveConstructor">r1</a><a id="3823" class="Symbol">)</a> <a id="3825" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3827" class="Symbol">λ</a> <a id="3829" class="Symbol">()</a>

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

<a id="4970" class="Keyword">module</a> <a id="solution-2-2"></a><a id="4977" href="Exercises.Complexity.FiniteCSP.html#4977" class="Module">solution-2-2</a> <a id="4990" class="Keyword">where</a>

 <a id="4998" class="Comment">-- The (purely) relational structure with</a>
 <a id="5041" class="Comment">-- + 2-element domain,</a>
 <a id="5065" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5116" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5172" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5177" href="Exercises.Complexity.FiniteCSP.html#5177" class="Datatype">Rᵃ</a> <a id="5180" class="Symbol">:</a> <a id="5182" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5187" class="Symbol">(</a><a id="5188" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5190" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5192" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a><a id="5193" class="Symbol">)</a> <a id="5195" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5198" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5206" href="Exercises.Complexity.FiniteCSP.html#5206" class="InductiveConstructor">r1</a> <a id="5209" class="Symbol">:</a> <a id="5211" class="Symbol">(</a><a id="5212" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5216" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5218" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5222" class="Symbol">)</a> <a id="5224" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5226" href="Exercises.Complexity.FiniteCSP.html#5177" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5231" href="Exercises.Complexity.FiniteCSP.html#5231" class="InductiveConstructor">r2</a> <a id="5234" class="Symbol">:</a> <a id="5236" class="Symbol">(</a><a id="5237" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5241" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5243" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5247" class="Symbol">)</a> <a id="5249" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5251" href="Exercises.Complexity.FiniteCSP.html#5177" class="Datatype">Rᵃ</a>

 <a id="5256" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5261" href="Exercises.Complexity.FiniteCSP.html#5261" class="Datatype">C₀ᵃ</a> <a id="5265" class="Symbol">:</a> <a id="5267" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5272" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5274" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5277" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5285" href="Exercises.Complexity.FiniteCSP.html#5285" class="InductiveConstructor">c₀</a> <a id="5288" class="Symbol">:</a> <a id="5290" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5294" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5296" href="Exercises.Complexity.FiniteCSP.html#5261" class="Datatype">C₀ᵃ</a>

 <a id="5302" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5307" href="Exercises.Complexity.FiniteCSP.html#5307" class="Datatype">C₁ᵃ</a> <a id="5311" class="Symbol">:</a> <a id="5313" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5318" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5320" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5323" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5331" href="Exercises.Complexity.FiniteCSP.html#5331" class="InductiveConstructor">c₁</a> <a id="5334" class="Symbol">:</a> <a id="5336" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5340" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5342" href="Exercises.Complexity.FiniteCSP.html#5307" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5349" href="Exercises.Complexity.FiniteCSP.html#5349" class="Function">𝑨</a> <a id="5351" class="Symbol">:</a> <a id="5353" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="5363" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="5369" class="Comment">-- (no operations)</a>
               <a id="5403" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a>  <a id="5409" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5460" href="Exercises.Complexity.FiniteCSP.html#5349" class="Function">𝑨</a> <a id="5462" class="Symbol">=</a> <a id="5464" class="Keyword">record</a> <a id="5471" class="Symbol">{</a> <a id="5473" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="5481" class="Symbol">=</a> <a id="5483" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a>
            <a id="5497" class="Symbol">;</a> <a id="5499" href="Structures.Basic.html#1739" class="Field">op</a> <a id="5502" class="Symbol">=</a> <a id="5504" class="Symbol">λ</a> <a id="5506" class="Symbol">()</a>
            <a id="5521" class="Symbol">;</a> <a id="5523" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="5527" class="Symbol">=</a> <a id="5529" href="Exercises.Complexity.FiniteCSP.html#5578" class="Function">rels</a>
            <a id="5546" class="Symbol">}</a>
            <a id="5560" class="Keyword">where</a>
            <a id="5578" href="Exercises.Complexity.FiniteCSP.html#5578" class="Function">rels</a> <a id="5583" class="Symbol">:</a> <a id="5585" class="Symbol">(</a><a id="5586" href="Exercises.Complexity.FiniteCSP.html#5586" class="Bound">r</a> <a id="5588" class="Symbol">:</a> <a id="5590" href="Overture.Preliminaries.html#3845" class="Datatype">𝟛</a><a id="5591" class="Symbol">)</a> <a id="5593" class="Symbol">→</a> <a id="5595" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="5599" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5601" class="Symbol">(</a><a id="5602" href="Structures.Basic.html#1313" class="Field">arity</a> <a id="5608" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a> <a id="5613" href="Exercises.Complexity.FiniteCSP.html#5586" class="Bound">r</a><a id="5614" class="Symbol">)</a>
            <a id="5628" href="Exercises.Complexity.FiniteCSP.html#5578" class="Function">rels</a> <a id="5633" href="Overture.Preliminaries.html#3864" class="InductiveConstructor">𝟛.𝟎</a> <a id="5637" href="Exercises.Complexity.FiniteCSP.html#5637" class="Bound">x</a> <a id="5639" class="Symbol">=</a> <a id="5641" class="Symbol">((</a><a id="5643" href="Exercises.Complexity.FiniteCSP.html#5637" class="Bound">x</a> <a id="5645" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="5648" class="Symbol">)</a> <a id="5650" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5652" class="Symbol">(</a><a id="5653" href="Exercises.Complexity.FiniteCSP.html#5637" class="Bound">x</a> <a id="5655" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a><a id="5658" class="Symbol">))</a> <a id="5661" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5663" href="Exercises.Complexity.FiniteCSP.html#5177" class="Datatype">Rᵃ</a>
            <a id="5678" href="Exercises.Complexity.FiniteCSP.html#5578" class="Function">rels</a> <a id="5683" href="Overture.Preliminaries.html#3873" class="InductiveConstructor">𝟛.𝟏</a> <a id="5687" href="Exercises.Complexity.FiniteCSP.html#5687" class="Bound">x</a> <a id="5689" class="Symbol">=</a> <a id="5691" href="Exercises.Complexity.FiniteCSP.html#5687" class="Bound">x</a> <a id="5693" href="Overture.Preliminaries.html#3712" class="InductiveConstructor">𝟙.𝟎</a> <a id="5697" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5699" href="Exercises.Complexity.FiniteCSP.html#5261" class="Datatype">C₀ᵃ</a>
            <a id="5715" href="Exercises.Complexity.FiniteCSP.html#5578" class="Function">rels</a> <a id="5720" href="Overture.Preliminaries.html#3882" class="InductiveConstructor">𝟛.𝟐</a> <a id="5724" href="Exercises.Complexity.FiniteCSP.html#5724" class="Bound">x</a> <a id="5726" class="Symbol">=</a> <a id="5728" href="Exercises.Complexity.FiniteCSP.html#5724" class="Bound">x</a> <a id="5730" href="Overture.Preliminaries.html#3712" class="InductiveConstructor">𝟙.𝟎</a> <a id="5734" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5736" href="Exercises.Complexity.FiniteCSP.html#5307" class="Datatype">C₁ᵃ</a>


 <a id="5743" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5847" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5893" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5929" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6000" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6078" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6158" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6206" class="Comment">--          )</a>
 <a id="6221" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6242" class="Comment">-- claim 𝑩 x = {!!}</a>

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


