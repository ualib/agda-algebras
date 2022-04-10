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
<a id="822" class="Keyword">open</a> <a id="827" class="Keyword">import</a> <a id="834" href="Base.Overture.Preliminaries.html" class="Module">Base.Overture.Preliminaries</a>         <a id="870" class="Keyword">using</a> <a id="876" class="Symbol">(</a> <a id="878" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="880" class="Symbol">;</a> <a id="882" href="Base.Overture.Preliminaries.html#3858" class="Datatype">𝟛</a> <a id="884" class="Symbol">)</a>
<a id="886" class="Keyword">open</a> <a id="891" class="Keyword">import</a> <a id="898" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>           <a id="934" class="Keyword">using</a> <a id="940" class="Symbol">(</a> <a id="942" href="Base.Relations.Continuous.html#3937" class="Function">Rel</a> <a id="946" class="Symbol">)</a>
<a id="948" class="Keyword">open</a> <a id="953" class="Keyword">import</a> <a id="960" href="Base.Structures.Basic.html" class="Module">Base.Structures.Basic</a>               <a id="996" class="Keyword">using</a> <a id="1002" class="Symbol">(</a> <a id="1004" href="Base.Structures.Basic.html#1264" class="Record">signature</a> <a id="1014" class="Symbol">;</a> <a id="1016" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="1026" class="Symbol">)</a>
<a id="1028" class="Keyword">open</a> <a id="1033" class="Keyword">import</a> <a id="1040" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="1071" class="Keyword">using</a> <a id="1077" class="Symbol">(</a> <a id="1079" href="Examples.Structures.Signatures.html#710" class="Function">S∅</a> <a id="1082" class="Symbol">;</a> <a id="1084" href="Examples.Structures.Signatures.html#1038" class="Function">S001</a> <a id="1089" class="Symbol">;</a> <a id="1091" href="Examples.Structures.Signatures.html#1293" class="Function">S021</a><a id="1095" class="Symbol">)</a>
<a id="1097" class="Keyword">open</a> <a id="1102" class="Keyword">import</a> <a id="1109" href="Base.Structures.Homs.html" class="Module">Base.Structures.Homs</a>                <a id="1145" class="Keyword">using</a> <a id="1151" class="Symbol">(</a> <a id="1153" href="Base.Structures.Homs.html#2869" class="Function">hom</a> <a id="1157" class="Symbol">)</a>
<a id="1159" class="Keyword">open</a> <a id="1164" href="Base.Structures.Basic.html#1264" class="Module">signature</a>
<a id="1174" class="Keyword">open</a> <a id="1179" href="Base.Structures.Basic.html#1598" class="Module">structure</a>

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
<a id="3229" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3236" href="Exercises.Complexity.FiniteCSP.html#3236" class="Module">solution-2-1</a> <a id="3249" class="Keyword">where</a>

 <a id="3257" class="Comment">-- The (purely) relational structure with</a>
 <a id="3300" class="Comment">-- + 2-element domain,</a>
 <a id="3324" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3375" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3380" href="Exercises.Complexity.FiniteCSP.html#3380" class="Datatype">Rᵃ</a> <a id="3383" class="Symbol">:</a> <a id="3385" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3390" class="Symbol">(</a><a id="3391" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="3393" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3395" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a><a id="3396" class="Symbol">)</a> <a id="3398" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="3401" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3409" href="Exercises.Complexity.FiniteCSP.html#3409" class="InductiveConstructor">r1</a> <a id="3412" class="Symbol">:</a> <a id="3414" class="Symbol">(</a><a id="3415" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a> <a id="3419" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3421" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a> <a id="3425" class="Symbol">)</a> <a id="3427" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3429" href="Exercises.Complexity.FiniteCSP.html#3380" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3434" href="Exercises.Complexity.FiniteCSP.html#3434" class="InductiveConstructor">r2</a> <a id="3437" class="Symbol">:</a> <a id="3439" class="Symbol">(</a><a id="3440" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a> <a id="3444" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3446" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a> <a id="3450" class="Symbol">)</a> <a id="3452" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3454" href="Exercises.Complexity.FiniteCSP.html#3380" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3459" href="Exercises.Complexity.FiniteCSP.html#3459" class="Function">𝑨</a> <a id="3461" class="Symbol">:</a> <a id="3463" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="3473" href="Examples.Structures.Signatures.html#710" class="Function">S∅</a>    <a id="3479" class="Comment">-- (no operation symbols)</a>
               <a id="3520" href="Examples.Structures.Signatures.html#1038" class="Function">S001</a>  <a id="3526" class="Comment">-- (one binary relation symbol)</a>

 <a id="3560" href="Exercises.Complexity.FiniteCSP.html#3459" class="Function">𝑨</a> <a id="3562" class="Symbol">=</a> <a id="3564" class="Keyword">record</a> <a id="3571" class="Symbol">{</a> <a id="3573" href="Base.Structures.Basic.html#1750" class="Field">carrier</a> <a id="3581" class="Symbol">=</a> <a id="3583" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a>
            <a id="3597" class="Symbol">;</a> <a id="3599" href="Base.Structures.Basic.html#1769" class="Field">op</a> <a id="3602" class="Symbol">=</a> <a id="3604" class="Symbol">λ</a> <a id="3606" class="Symbol">()</a>
            <a id="3621" class="Symbol">;</a> <a id="3623" href="Base.Structures.Basic.html#1853" class="Field">rel</a> <a id="3627" class="Symbol">=</a> <a id="3629" class="Symbol">λ</a> <a id="3631" href="Exercises.Complexity.FiniteCSP.html#3631" class="Bound">_</a> <a id="3633" href="Exercises.Complexity.FiniteCSP.html#3633" class="Bound">x</a> <a id="3635" class="Symbol">→</a> <a id="3637" class="Symbol">((</a><a id="3639" href="Exercises.Complexity.FiniteCSP.html#3633" class="Bound">x</a> <a id="3641" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a><a id="3644" class="Symbol">)</a> <a id="3646" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3648" class="Symbol">(</a><a id="3649" href="Exercises.Complexity.FiniteCSP.html#3633" class="Bound">x</a> <a id="3651" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a><a id="3654" class="Symbol">))</a> <a id="3657" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3659" href="Exercises.Complexity.FiniteCSP.html#3380" class="Datatype">Rᵃ</a>
            <a id="3674" class="Symbol">}</a>


 <a id="3679" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3787" href="Exercises.Complexity.FiniteCSP.html#3787" class="Function">claim</a> <a id="3793" class="Symbol">:</a> <a id="3795" class="Symbol">(</a><a id="3796" href="Exercises.Complexity.FiniteCSP.html#3796" class="Bound">𝑩</a> <a id="3798" class="Symbol">:</a> <a id="3800" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="3810" class="Symbol">{</a><a id="3811" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3813" class="Symbol">}{</a><a id="3815" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3817" class="Symbol">}{</a><a id="3819" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3821" class="Symbol">}{</a><a id="3823" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3825" class="Symbol">}</a> <a id="3827" href="Examples.Structures.Signatures.html#710" class="Function">S∅</a> <a id="3830" href="Examples.Structures.Signatures.html#1038" class="Function">S001</a> <a id="3835" class="Symbol">{</a><a id="3836" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3838" class="Symbol">}{</a><a id="3840" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3842" class="Symbol">})</a> <a id="3845" class="Symbol">→</a> <a id="3847" href="Base.Structures.Homs.html#2869" class="Function">hom</a> <a id="3851" href="Exercises.Complexity.FiniteCSP.html#3796" class="Bound">𝑩</a> <a id="3853" href="Exercises.Complexity.FiniteCSP.html#3459" class="Function">𝑨</a>
 <a id="3856" href="Exercises.Complexity.FiniteCSP.html#3787" class="Function">claim</a> <a id="3862" href="Exercises.Complexity.FiniteCSP.html#3862" class="Bound">𝑩</a> <a id="3864" class="Symbol">=</a> <a id="3866" class="Symbol">(λ</a> <a id="3869" href="Exercises.Complexity.FiniteCSP.html#3869" class="Bound">x</a> <a id="3871" class="Symbol">→</a> <a id="3873" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a><a id="3876" class="Symbol">)</a> <a id="3878" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3880" class="Symbol">(λ</a> <a id="3883" href="Exercises.Complexity.FiniteCSP.html#3883" class="Bound">_</a> <a id="3885" href="Exercises.Complexity.FiniteCSP.html#3885" class="Bound">_</a> <a id="3887" href="Exercises.Complexity.FiniteCSP.html#3887" class="Bound">_</a> <a id="3889" class="Symbol">→</a> <a id="3891" href="Exercises.Complexity.FiniteCSP.html#3409" class="InductiveConstructor">r1</a><a id="3893" class="Symbol">)</a> <a id="3895" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3897" class="Symbol">λ</a> <a id="3899" class="Symbol">()</a>

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

<a id="5040" class="Keyword">module</a> <a id="solution-2-2"></a><a id="5047" href="Exercises.Complexity.FiniteCSP.html#5047" class="Module">solution-2-2</a> <a id="5060" class="Keyword">where</a>

 <a id="5068" class="Comment">-- The (purely) relational structure with</a>
 <a id="5111" class="Comment">-- + 2-element domain,</a>
 <a id="5135" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5186" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5242" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5247" href="Exercises.Complexity.FiniteCSP.html#5247" class="Datatype">Rᵃ</a> <a id="5250" class="Symbol">:</a> <a id="5252" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5257" class="Symbol">(</a><a id="5258" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="5260" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5262" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a><a id="5263" class="Symbol">)</a> <a id="5265" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5268" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5276" href="Exercises.Complexity.FiniteCSP.html#5276" class="InductiveConstructor">r1</a> <a id="5279" class="Symbol">:</a> <a id="5281" class="Symbol">(</a><a id="5282" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a> <a id="5286" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5288" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a> <a id="5292" class="Symbol">)</a> <a id="5294" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5296" href="Exercises.Complexity.FiniteCSP.html#5247" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5301" href="Exercises.Complexity.FiniteCSP.html#5301" class="InductiveConstructor">r2</a> <a id="5304" class="Symbol">:</a> <a id="5306" class="Symbol">(</a><a id="5307" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a> <a id="5311" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5313" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a> <a id="5317" class="Symbol">)</a> <a id="5319" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5321" href="Exercises.Complexity.FiniteCSP.html#5247" class="Datatype">Rᵃ</a>

 <a id="5326" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5331" href="Exercises.Complexity.FiniteCSP.html#5331" class="Datatype">C₀ᵃ</a> <a id="5335" class="Symbol">:</a> <a id="5337" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5342" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="5344" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5347" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5355" href="Exercises.Complexity.FiniteCSP.html#5355" class="InductiveConstructor">c₀</a> <a id="5358" class="Symbol">:</a> <a id="5360" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a> <a id="5364" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5366" href="Exercises.Complexity.FiniteCSP.html#5331" class="Datatype">C₀ᵃ</a>

 <a id="5372" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5377" href="Exercises.Complexity.FiniteCSP.html#5377" class="Datatype">C₁ᵃ</a> <a id="5381" class="Symbol">:</a> <a id="5383" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5388" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="5390" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5393" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5401" href="Exercises.Complexity.FiniteCSP.html#5401" class="InductiveConstructor">c₁</a> <a id="5404" class="Symbol">:</a> <a id="5406" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a> <a id="5410" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5412" href="Exercises.Complexity.FiniteCSP.html#5377" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5419" href="Exercises.Complexity.FiniteCSP.html#5419" class="Function">𝑨</a> <a id="5421" class="Symbol">:</a> <a id="5423" href="Base.Structures.Basic.html#1598" class="Record">structure</a> <a id="5433" href="Examples.Structures.Signatures.html#710" class="Function">S∅</a>    <a id="5439" class="Comment">-- (no operations)</a>
               <a id="5473" href="Examples.Structures.Signatures.html#1293" class="Function">S021</a>  <a id="5479" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5530" href="Exercises.Complexity.FiniteCSP.html#5419" class="Function">𝑨</a> <a id="5532" class="Symbol">=</a> <a id="5534" class="Keyword">record</a> <a id="5541" class="Symbol">{</a> <a id="5543" href="Base.Structures.Basic.html#1750" class="Field">carrier</a> <a id="5551" class="Symbol">=</a> <a id="5553" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a>
            <a id="5567" class="Symbol">;</a> <a id="5569" href="Base.Structures.Basic.html#1769" class="Field">op</a> <a id="5572" class="Symbol">=</a> <a id="5574" class="Symbol">λ</a> <a id="5576" class="Symbol">()</a>
            <a id="5591" class="Symbol">;</a> <a id="5593" href="Base.Structures.Basic.html#1853" class="Field">rel</a> <a id="5597" class="Symbol">=</a> <a id="5599" href="Exercises.Complexity.FiniteCSP.html#5648" class="Function">rels</a>
            <a id="5616" class="Symbol">}</a>
            <a id="5630" class="Keyword">where</a>
            <a id="5648" href="Exercises.Complexity.FiniteCSP.html#5648" class="Function">rels</a> <a id="5653" class="Symbol">:</a> <a id="5655" class="Symbol">(</a><a id="5656" href="Exercises.Complexity.FiniteCSP.html#5656" class="Bound">r</a> <a id="5658" class="Symbol">:</a> <a id="5660" href="Base.Overture.Preliminaries.html#3858" class="Datatype">𝟛</a><a id="5661" class="Symbol">)</a> <a id="5663" class="Symbol">→</a> <a id="5665" href="Base.Relations.Continuous.html#3937" class="Function">Rel</a> <a id="5669" href="Base.Overture.Preliminaries.html#3761" class="Datatype">𝟚</a> <a id="5671" class="Symbol">(</a><a id="5672" href="Base.Structures.Basic.html#1343" class="Field">arity</a> <a id="5678" href="Examples.Structures.Signatures.html#1293" class="Function">S021</a> <a id="5683" href="Exercises.Complexity.FiniteCSP.html#5656" class="Bound">r</a><a id="5684" class="Symbol">)</a>
            <a id="5698" href="Exercises.Complexity.FiniteCSP.html#5648" class="Function">rels</a> <a id="5703" href="Base.Overture.Preliminaries.html#3877" class="InductiveConstructor">𝟛.𝟎</a> <a id="5707" href="Exercises.Complexity.FiniteCSP.html#5707" class="Bound">x</a> <a id="5709" class="Symbol">=</a> <a id="5711" class="Symbol">((</a><a id="5713" href="Exercises.Complexity.FiniteCSP.html#5707" class="Bound">x</a> <a id="5715" href="Base.Overture.Preliminaries.html#3811" class="InductiveConstructor">𝟚.𝟎</a><a id="5718" class="Symbol">)</a> <a id="5720" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5722" class="Symbol">(</a><a id="5723" href="Exercises.Complexity.FiniteCSP.html#5707" class="Bound">x</a> <a id="5725" href="Base.Overture.Preliminaries.html#3820" class="InductiveConstructor">𝟚.𝟏</a><a id="5728" class="Symbol">))</a> <a id="5731" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5733" href="Exercises.Complexity.FiniteCSP.html#5247" class="Datatype">Rᵃ</a>
            <a id="5748" href="Exercises.Complexity.FiniteCSP.html#5648" class="Function">rels</a> <a id="5753" href="Base.Overture.Preliminaries.html#3886" class="InductiveConstructor">𝟛.𝟏</a> <a id="5757" href="Exercises.Complexity.FiniteCSP.html#5757" class="Bound">x</a> <a id="5759" class="Symbol">=</a> <a id="5761" href="Exercises.Complexity.FiniteCSP.html#5757" class="Bound">x</a> <a id="5763" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5765" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5767" href="Exercises.Complexity.FiniteCSP.html#5331" class="Datatype">C₀ᵃ</a>
            <a id="5783" href="Exercises.Complexity.FiniteCSP.html#5648" class="Function">rels</a> <a id="5788" href="Base.Overture.Preliminaries.html#3895" class="InductiveConstructor">𝟛.𝟐</a> <a id="5792" href="Exercises.Complexity.FiniteCSP.html#5792" class="Bound">x</a> <a id="5794" class="Symbol">=</a> <a id="5796" href="Exercises.Complexity.FiniteCSP.html#5792" class="Bound">x</a> <a id="5798" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5800" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5802" href="Exercises.Complexity.FiniteCSP.html#5377" class="Datatype">C₁ᵃ</a>


 <a id="5809" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5913" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5959" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5995" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6066" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6144" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6224" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6272" class="Comment">--          )</a>
 <a id="6287" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6308" class="Comment">-- claim 𝑩 x = {!!}</a>

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


