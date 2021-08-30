---
layout: default
title : "Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team][] and Libor Bar"
---

⁺All excercises below were made by Libor Barto (for students at Charles University), and formalized in MLTT/Agda by the [agda-algebras development team][].

### CSP Exercises

<pre class="Agda">

<a id="379" class="Symbol">{-#</a> <a id="383" class="Keyword">OPTIONS</a> <a id="391" class="Pragma">--without-K</a> <a id="403" class="Pragma">--exact-split</a> <a id="417" class="Pragma">--safe</a> <a id="424" class="Symbol">#-}</a>

<a id="429" class="Keyword">module</a> <a id="436" href="Exercises.Complexity.FiniteCSP.html" class="Module">Exercises.Complexity.FiniteCSP</a>  <a id="468" class="Keyword">where</a>

<a id="475" class="Keyword">open</a> <a id="480" class="Keyword">import</a> <a id="487" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a> <a id="511" class="Symbol">)</a> <a id="513" class="Keyword">renaming</a> <a id="522" class="Symbol">(</a><a id="523" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="529" class="Symbol">to</a> <a id="532" class="Primitive">ℓ₀</a> <a id="535" class="Symbol">)</a>
<a id="537" class="Keyword">open</a> <a id="542" class="Keyword">import</a> <a id="549" href="Data.Product.html" class="Module">Data.Product</a>    <a id="565" class="Keyword">using</a> <a id="571" class="Symbol">(</a> <a id="573" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="577" class="Symbol">;</a> <a id="579" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="583" class="Symbol">)</a>
<a id="585" class="Keyword">open</a> <a id="590" class="Keyword">import</a> <a id="597" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="613" class="Keyword">using</a> <a id="619" class="Symbol">(</a> <a id="621" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="626" class="Symbol">;</a> <a id="628" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="632" class="Symbol">)</a>

<a id="635" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="728" class="Keyword">open</a> <a id="733" class="Keyword">import</a> <a id="740" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>         <a id="771" class="Keyword">using</a> <a id="777" class="Symbol">(</a> <a id="779" href="Overture.Preliminaries.html#3613" class="Datatype">𝟘</a> <a id="781" class="Symbol">;</a> <a id="783" href="Overture.Preliminaries.html#3689" class="Datatype">𝟙</a> <a id="785" class="Symbol">;</a> <a id="787" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="789" class="Symbol">;</a> <a id="791" href="Overture.Preliminaries.html#3841" class="Datatype">𝟛</a> <a id="793" class="Symbol">)</a>
<a id="795" class="Keyword">open</a> <a id="800" class="Keyword">import</a> <a id="807" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>           <a id="838" class="Keyword">using</a> <a id="844" class="Symbol">(</a> <a id="846" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="850" class="Symbol">)</a>
<a id="852" class="Keyword">open</a> <a id="857" class="Keyword">import</a> <a id="864" href="Structures.Basic.html" class="Module">Structures.Basic</a>               <a id="895" class="Keyword">using</a> <a id="901" class="Symbol">(</a> <a id="903" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="913" class="Symbol">;</a> <a id="915" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="925" class="Symbol">)</a>
<a id="927" class="Keyword">open</a> <a id="932" class="Keyword">import</a> <a id="939" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="970" class="Keyword">using</a> <a id="976" class="Symbol">(</a> <a id="978" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="981" class="Symbol">;</a> <a id="983" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="988" class="Symbol">;</a> <a id="990" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a><a id="994" class="Symbol">)</a>
<a id="996" class="Keyword">open</a> <a id="1001" class="Keyword">import</a> <a id="1008" href="Structures.Homs.html" class="Module">Structures.Homs</a>                <a id="1039" class="Keyword">using</a> <a id="1045" class="Symbol">(</a> <a id="1047" href="Structures.Homs.html#2693" class="Function">hom</a> <a id="1051" class="Symbol">)</a>
<a id="1053" class="Keyword">open</a> <a id="1058" href="Structures.Basic.html#1234" class="Module">signature</a>
<a id="1068" class="Keyword">open</a> <a id="1073" href="Structures.Basic.html#1568" class="Module">structure</a>

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
<a id="3123" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3130" href="Exercises.Complexity.FiniteCSP.html#3130" class="Module">solution-2-1</a> <a id="3143" class="Keyword">where</a>

 <a id="3151" class="Comment">-- The (purely) relational structure with</a>
 <a id="3194" class="Comment">-- + 2-element domain,</a>
 <a id="3218" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3269" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3274" href="Exercises.Complexity.FiniteCSP.html#3274" class="Datatype">Rᵃ</a> <a id="3277" class="Symbol">:</a> <a id="3279" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3284" class="Symbol">(</a><a id="3285" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="3287" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3289" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a><a id="3290" class="Symbol">)</a> <a id="3292" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a> <a id="3295" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3303" href="Exercises.Complexity.FiniteCSP.html#3303" class="InductiveConstructor">r1</a> <a id="3306" class="Symbol">:</a> <a id="3308" class="Symbol">(</a><a id="3309" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a> <a id="3313" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3315" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a> <a id="3319" class="Symbol">)</a> <a id="3321" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3323" href="Exercises.Complexity.FiniteCSP.html#3274" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3328" href="Exercises.Complexity.FiniteCSP.html#3328" class="InductiveConstructor">r2</a> <a id="3331" class="Symbol">:</a> <a id="3333" class="Symbol">(</a><a id="3334" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a> <a id="3338" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3340" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a> <a id="3344" class="Symbol">)</a> <a id="3346" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3348" href="Exercises.Complexity.FiniteCSP.html#3274" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3353" href="Exercises.Complexity.FiniteCSP.html#3353" class="Function">𝑨</a> <a id="3355" class="Symbol">:</a> <a id="3357" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3367" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="3373" class="Comment">-- (no operation symbols)</a>
               <a id="3414" href="Examples.Structures.Signatures.html#893" class="Function">S001</a>  <a id="3420" class="Comment">-- (one binary relation symbol)</a>

 <a id="3454" href="Exercises.Complexity.FiniteCSP.html#3353" class="Function">𝑨</a> <a id="3456" class="Symbol">=</a> <a id="3458" class="Keyword">record</a> <a id="3465" class="Symbol">{</a> <a id="3467" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="3475" class="Symbol">=</a> <a id="3477" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a>
            <a id="3491" class="Symbol">;</a> <a id="3493" href="Structures.Basic.html#1739" class="Field">op</a> <a id="3496" class="Symbol">=</a> <a id="3498" class="Symbol">λ</a> <a id="3500" class="Symbol">()</a>
            <a id="3515" class="Symbol">;</a> <a id="3517" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="3521" class="Symbol">=</a> <a id="3523" class="Symbol">λ</a> <a id="3525" href="Exercises.Complexity.FiniteCSP.html#3525" class="Bound">_</a> <a id="3527" href="Exercises.Complexity.FiniteCSP.html#3527" class="Bound">x</a> <a id="3529" class="Symbol">→</a> <a id="3531" class="Symbol">((</a><a id="3533" href="Exercises.Complexity.FiniteCSP.html#3527" class="Bound">x</a> <a id="3535" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a><a id="3538" class="Symbol">)</a> <a id="3540" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3542" class="Symbol">(</a><a id="3543" href="Exercises.Complexity.FiniteCSP.html#3527" class="Bound">x</a> <a id="3545" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a><a id="3548" class="Symbol">))</a> <a id="3551" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3553" href="Exercises.Complexity.FiniteCSP.html#3274" class="Datatype">Rᵃ</a>
            <a id="3568" class="Symbol">}</a>


 <a id="3573" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3681" href="Exercises.Complexity.FiniteCSP.html#3681" class="Function">claim</a> <a id="3687" class="Symbol">:</a> <a id="3689" class="Symbol">(</a><a id="3690" href="Exercises.Complexity.FiniteCSP.html#3690" class="Bound">𝑩</a> <a id="3692" class="Symbol">:</a> <a id="3694" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3704" class="Symbol">{</a><a id="3705" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3707" class="Symbol">}{</a><a id="3709" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3711" class="Symbol">}{</a><a id="3713" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3715" class="Symbol">}{</a><a id="3717" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3719" class="Symbol">}</a> <a id="3721" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="3724" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="3729" class="Symbol">{</a><a id="3730" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3732" class="Symbol">}{</a><a id="3734" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a><a id="3736" class="Symbol">})</a> <a id="3739" class="Symbol">→</a> <a id="3741" href="Structures.Homs.html#2693" class="Function">hom</a> <a id="3745" href="Exercises.Complexity.FiniteCSP.html#3690" class="Bound">𝑩</a> <a id="3747" href="Exercises.Complexity.FiniteCSP.html#3353" class="Function">𝑨</a>
 <a id="3750" href="Exercises.Complexity.FiniteCSP.html#3681" class="Function">claim</a> <a id="3756" href="Exercises.Complexity.FiniteCSP.html#3756" class="Bound">𝑩</a> <a id="3758" class="Symbol">=</a> <a id="3760" class="Symbol">(λ</a> <a id="3763" href="Exercises.Complexity.FiniteCSP.html#3763" class="Bound">x</a> <a id="3765" class="Symbol">→</a> <a id="3767" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a><a id="3770" class="Symbol">)</a> <a id="3772" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3774" class="Symbol">(λ</a> <a id="3777" href="Exercises.Complexity.FiniteCSP.html#3777" class="Bound">_</a> <a id="3779" href="Exercises.Complexity.FiniteCSP.html#3779" class="Bound">_</a> <a id="3781" href="Exercises.Complexity.FiniteCSP.html#3781" class="Bound">_</a> <a id="3783" class="Symbol">→</a> <a id="3785" href="Exercises.Complexity.FiniteCSP.html#3303" class="InductiveConstructor">r1</a><a id="3787" class="Symbol">)</a> <a id="3789" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3791" class="Symbol">λ</a> <a id="3793" class="Symbol">()</a>

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

<a id="4934" class="Keyword">module</a> <a id="solution-2-2"></a><a id="4941" href="Exercises.Complexity.FiniteCSP.html#4941" class="Module">solution-2-2</a> <a id="4954" class="Keyword">where</a>

 <a id="4962" class="Comment">-- The (purely) relational structure with</a>
 <a id="5005" class="Comment">-- + 2-element domain,</a>
 <a id="5029" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5080" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5136" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5141" href="Exercises.Complexity.FiniteCSP.html#5141" class="Datatype">Rᵃ</a> <a id="5144" class="Symbol">:</a> <a id="5146" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5151" class="Symbol">(</a><a id="5152" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="5154" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5156" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a><a id="5157" class="Symbol">)</a> <a id="5159" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a> <a id="5162" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5170" href="Exercises.Complexity.FiniteCSP.html#5170" class="InductiveConstructor">r1</a> <a id="5173" class="Symbol">:</a> <a id="5175" class="Symbol">(</a><a id="5176" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a> <a id="5180" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5182" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a> <a id="5186" class="Symbol">)</a> <a id="5188" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5190" href="Exercises.Complexity.FiniteCSP.html#5141" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5195" href="Exercises.Complexity.FiniteCSP.html#5195" class="InductiveConstructor">r2</a> <a id="5198" class="Symbol">:</a> <a id="5200" class="Symbol">(</a><a id="5201" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a> <a id="5205" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5207" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a> <a id="5211" class="Symbol">)</a> <a id="5213" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5215" href="Exercises.Complexity.FiniteCSP.html#5141" class="Datatype">Rᵃ</a>

 <a id="5220" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5225" href="Exercises.Complexity.FiniteCSP.html#5225" class="Datatype">C₀ᵃ</a> <a id="5229" class="Symbol">:</a> <a id="5231" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5236" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="5238" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a> <a id="5241" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5249" href="Exercises.Complexity.FiniteCSP.html#5249" class="InductiveConstructor">c₀</a> <a id="5252" class="Symbol">:</a> <a id="5254" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a> <a id="5258" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5260" href="Exercises.Complexity.FiniteCSP.html#5225" class="Datatype">C₀ᵃ</a>

 <a id="5266" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5271" href="Exercises.Complexity.FiniteCSP.html#5271" class="Datatype">C₁ᵃ</a> <a id="5275" class="Symbol">:</a> <a id="5277" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5282" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="5284" href="Exercises.Complexity.FiniteCSP.html#532" class="Primitive">ℓ₀</a> <a id="5287" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5295" href="Exercises.Complexity.FiniteCSP.html#5295" class="InductiveConstructor">c₁</a> <a id="5298" class="Symbol">:</a> <a id="5300" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a> <a id="5304" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5306" href="Exercises.Complexity.FiniteCSP.html#5271" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5313" href="Exercises.Complexity.FiniteCSP.html#5313" class="Function">𝑨</a> <a id="5315" class="Symbol">:</a> <a id="5317" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="5327" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="5333" class="Comment">-- (no operations)</a>
               <a id="5367" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a>  <a id="5373" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5424" href="Exercises.Complexity.FiniteCSP.html#5313" class="Function">𝑨</a> <a id="5426" class="Symbol">=</a> <a id="5428" class="Keyword">record</a> <a id="5435" class="Symbol">{</a> <a id="5437" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="5445" class="Symbol">=</a> <a id="5447" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a>
            <a id="5461" class="Symbol">;</a> <a id="5463" href="Structures.Basic.html#1739" class="Field">op</a> <a id="5466" class="Symbol">=</a> <a id="5468" class="Symbol">λ</a> <a id="5470" class="Symbol">()</a>
            <a id="5485" class="Symbol">;</a> <a id="5487" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="5491" class="Symbol">=</a> <a id="5493" href="Exercises.Complexity.FiniteCSP.html#5542" class="Function">rels</a>
            <a id="5510" class="Symbol">}</a>
            <a id="5524" class="Keyword">where</a>
            <a id="5542" href="Exercises.Complexity.FiniteCSP.html#5542" class="Function">rels</a> <a id="5547" class="Symbol">:</a> <a id="5549" class="Symbol">(</a><a id="5550" href="Exercises.Complexity.FiniteCSP.html#5550" class="Bound">r</a> <a id="5552" class="Symbol">:</a> <a id="5554" href="Overture.Preliminaries.html#3841" class="Datatype">𝟛</a><a id="5555" class="Symbol">)</a> <a id="5557" class="Symbol">→</a> <a id="5559" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="5563" href="Overture.Preliminaries.html#3744" class="Datatype">𝟚</a> <a id="5565" class="Symbol">(</a><a id="5566" href="Structures.Basic.html#1313" class="Field">arity</a> <a id="5572" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a> <a id="5577" href="Exercises.Complexity.FiniteCSP.html#5550" class="Bound">r</a><a id="5578" class="Symbol">)</a>
            <a id="5592" href="Exercises.Complexity.FiniteCSP.html#5542" class="Function">rels</a> <a id="5597" href="Overture.Preliminaries.html#3860" class="InductiveConstructor">𝟛.𝟎</a> <a id="5601" href="Exercises.Complexity.FiniteCSP.html#5601" class="Bound">x</a> <a id="5603" class="Symbol">=</a> <a id="5605" class="Symbol">((</a><a id="5607" href="Exercises.Complexity.FiniteCSP.html#5601" class="Bound">x</a> <a id="5609" href="Overture.Preliminaries.html#3794" class="InductiveConstructor">𝟚.𝟎</a><a id="5612" class="Symbol">)</a> <a id="5614" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5616" class="Symbol">(</a><a id="5617" href="Exercises.Complexity.FiniteCSP.html#5601" class="Bound">x</a> <a id="5619" href="Overture.Preliminaries.html#3803" class="InductiveConstructor">𝟚.𝟏</a><a id="5622" class="Symbol">))</a> <a id="5625" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5627" href="Exercises.Complexity.FiniteCSP.html#5141" class="Datatype">Rᵃ</a>
            <a id="5642" href="Exercises.Complexity.FiniteCSP.html#5542" class="Function">rels</a> <a id="5647" href="Overture.Preliminaries.html#3869" class="InductiveConstructor">𝟛.𝟏</a> <a id="5651" href="Exercises.Complexity.FiniteCSP.html#5651" class="Bound">x</a> <a id="5653" class="Symbol">=</a> <a id="5655" href="Exercises.Complexity.FiniteCSP.html#5651" class="Bound">x</a> <a id="5657" href="Overture.Preliminaries.html#3708" class="InductiveConstructor">𝟙.𝟎</a> <a id="5661" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5663" href="Exercises.Complexity.FiniteCSP.html#5225" class="Datatype">C₀ᵃ</a>
            <a id="5679" href="Exercises.Complexity.FiniteCSP.html#5542" class="Function">rels</a> <a id="5684" href="Overture.Preliminaries.html#3878" class="InductiveConstructor">𝟛.𝟐</a> <a id="5688" href="Exercises.Complexity.FiniteCSP.html#5688" class="Bound">x</a> <a id="5690" class="Symbol">=</a> <a id="5692" href="Exercises.Complexity.FiniteCSP.html#5688" class="Bound">x</a> <a id="5694" href="Overture.Preliminaries.html#3708" class="InductiveConstructor">𝟙.𝟎</a> <a id="5698" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5700" href="Exercises.Complexity.FiniteCSP.html#5271" class="Datatype">C₁ᵃ</a>


 <a id="5707" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5811" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5857" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5893" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="5964" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6042" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6122" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6170" class="Comment">--          )</a>
 <a id="6185" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6206" class="Comment">-- claim 𝑩 x = {!!}</a>

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


