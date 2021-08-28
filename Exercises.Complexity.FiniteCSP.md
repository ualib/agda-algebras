---
layout: default
title : Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)
date : 2021-07-26
author: [agda-algebras development team][] and Libor Barto⁺
---

⁺All excercises below were made by Libor Barto (for students at Charles University), and formalized in MLTT/Agda by the [agda-algebras development team][].

### CSP Exercises

<pre class="Agda">

<a id="377" class="Symbol">{-#</a> <a id="381" class="Keyword">OPTIONS</a> <a id="389" class="Pragma">--without-K</a> <a id="401" class="Pragma">--exact-split</a> <a id="415" class="Pragma">--safe</a> <a id="422" class="Symbol">#-}</a>

<a id="427" class="Keyword">module</a> <a id="434" href="Exercises.Complexity.FiniteCSP.html" class="Module">Exercises.Complexity.FiniteCSP</a>  <a id="466" class="Keyword">where</a>


<a id="474" class="Keyword">open</a> <a id="479" class="Keyword">import</a> <a id="486" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="502" class="Keyword">using</a> <a id="508" class="Symbol">(</a> <a id="510" class="Symbol">)</a> <a id="512" class="Keyword">renaming</a> <a id="521" class="Symbol">(</a><a id="522" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="528" class="Symbol">to</a> <a id="531" class="Primitive">ℓ₀</a> <a id="534" class="Symbol">)</a>
<a id="536" class="Keyword">open</a> <a id="541" class="Keyword">import</a> <a id="548" href="Data.Product.html" class="Module">Data.Product</a>    <a id="564" class="Keyword">using</a> <a id="570" class="Symbol">(</a> <a id="572" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="576" class="Symbol">;</a> <a id="578" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="582" class="Symbol">)</a>
<a id="584" class="Keyword">open</a> <a id="589" class="Keyword">import</a> <a id="596" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="612" class="Keyword">using</a> <a id="618" class="Symbol">(</a> <a id="620" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="625" class="Symbol">;</a> <a id="627" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="631" class="Symbol">)</a>

<a id="634" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="727" class="Keyword">open</a> <a id="732" class="Keyword">import</a> <a id="739" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>         <a id="770" class="Keyword">using</a> <a id="776" class="Symbol">(</a> <a id="778" href="Overture.Preliminaries.html#3663" class="Datatype">𝟘</a> <a id="780" class="Symbol">;</a> <a id="782" href="Overture.Preliminaries.html#3750" class="Datatype">𝟙</a> <a id="784" class="Symbol">;</a> <a id="786" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="788" class="Symbol">;</a> <a id="790" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a> <a id="792" class="Symbol">)</a>
<a id="794" class="Keyword">open</a> <a id="799" class="Keyword">import</a> <a id="806" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>           <a id="837" class="Keyword">using</a> <a id="843" class="Symbol">(</a> <a id="845" href="Relations.Continuous.html#3898" class="Function">Rel</a> <a id="849" class="Symbol">)</a>
<a id="851" class="Keyword">open</a> <a id="856" class="Keyword">import</a> <a id="863" href="Structures.Basic.html" class="Module">Structures.Basic</a>               <a id="894" class="Keyword">using</a> <a id="900" class="Symbol">(</a> <a id="902" href="Structures.Basic.html#1231" class="Record">signature</a> <a id="912" class="Symbol">;</a> <a id="914" href="Structures.Basic.html#1565" class="Record">structure</a> <a id="924" class="Symbol">)</a>
<a id="926" class="Keyword">open</a> <a id="931" class="Keyword">import</a> <a id="938" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="969" class="Keyword">using</a> <a id="975" class="Symbol">(</a> <a id="977" href="Examples.Structures.Signatures.html#566" class="Function">S∅</a> <a id="980" class="Symbol">;</a> <a id="982" href="Examples.Structures.Signatures.html#894" class="Function">S001</a> <a id="987" class="Symbol">;</a> <a id="989" href="Examples.Structures.Signatures.html#1149" class="Function">S021</a><a id="993" class="Symbol">)</a>
<a id="995" class="Keyword">open</a> <a id="1000" class="Keyword">import</a> <a id="1007" href="Structures.Homs.html" class="Module">Structures.Homs</a>                <a id="1038" class="Keyword">using</a> <a id="1044" class="Symbol">(</a> <a id="1046" href="Structures.Homs.html#2728" class="Function">hom</a> <a id="1050" class="Symbol">)</a>

<a id="1053" class="Keyword">open</a> <a id="1058" href="Structures.Basic.html#1231" class="Module">signature</a>
<a id="1068" class="Keyword">open</a> <a id="1073" href="Structures.Basic.html#1565" class="Module">structure</a>
<a id="1083" class="Comment">-- open _⊎_</a>



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
<a id="3138" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3145" href="Exercises.Complexity.FiniteCSP.html#3145" class="Module">solution-2-1</a> <a id="3158" class="Keyword">where</a>

 <a id="3166" class="Comment">-- The (purely) relational structure with</a>
 <a id="3209" class="Comment">-- + 2-element domain,</a>
 <a id="3233" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3284" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3289" href="Exercises.Complexity.FiniteCSP.html#3289" class="Datatype">Rᵃ</a> <a id="3292" class="Symbol">:</a> <a id="3294" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3299" class="Symbol">(</a><a id="3300" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="3302" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3304" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a><a id="3305" class="Symbol">)</a> <a id="3307" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a> <a id="3310" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3318" href="Exercises.Complexity.FiniteCSP.html#3318" class="InductiveConstructor">r1</a> <a id="3321" class="Symbol">:</a> <a id="3323" class="Symbol">(</a><a id="3324" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a> <a id="3328" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3330" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a> <a id="3334" class="Symbol">)</a> <a id="3336" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3338" href="Exercises.Complexity.FiniteCSP.html#3289" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3343" href="Exercises.Complexity.FiniteCSP.html#3343" class="InductiveConstructor">r2</a> <a id="3346" class="Symbol">:</a> <a id="3348" class="Symbol">(</a><a id="3349" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a> <a id="3353" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3355" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a> <a id="3359" class="Symbol">)</a> <a id="3361" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3363" href="Exercises.Complexity.FiniteCSP.html#3289" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3368" href="Exercises.Complexity.FiniteCSP.html#3368" class="Function">𝑨</a> <a id="3370" class="Symbol">:</a> <a id="3372" href="Structures.Basic.html#1565" class="Record">structure</a> <a id="3382" href="Examples.Structures.Signatures.html#566" class="Function">S∅</a>    <a id="3388" class="Comment">-- (no operation symbols)</a>
               <a id="3429" href="Examples.Structures.Signatures.html#894" class="Function">S001</a>  <a id="3435" class="Comment">-- (one binary relation symbol)</a>

 <a id="3469" href="Exercises.Complexity.FiniteCSP.html#3368" class="Function">𝑨</a> <a id="3471" class="Symbol">=</a> <a id="3473" class="Keyword">record</a> <a id="3480" class="Symbol">{</a> <a id="3482" href="Structures.Basic.html#1717" class="Field">carrier</a> <a id="3490" class="Symbol">=</a> <a id="3492" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a>
            <a id="3506" class="Symbol">;</a> <a id="3508" href="Structures.Basic.html#1736" class="Field">op</a> <a id="3511" class="Symbol">=</a> <a id="3513" class="Symbol">λ</a> <a id="3515" class="Symbol">()</a>
            <a id="3530" class="Symbol">;</a> <a id="3532" href="Structures.Basic.html#1820" class="Field">rel</a> <a id="3536" class="Symbol">=</a> <a id="3538" class="Symbol">λ</a> <a id="3540" href="Exercises.Complexity.FiniteCSP.html#3540" class="Bound">_</a> <a id="3542" href="Exercises.Complexity.FiniteCSP.html#3542" class="Bound">x</a> <a id="3544" class="Symbol">→</a> <a id="3546" class="Symbol">((</a><a id="3548" href="Exercises.Complexity.FiniteCSP.html#3542" class="Bound">x</a> <a id="3550" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a><a id="3553" class="Symbol">)</a> <a id="3555" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3557" class="Symbol">(</a><a id="3558" href="Exercises.Complexity.FiniteCSP.html#3542" class="Bound">x</a> <a id="3560" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a><a id="3563" class="Symbol">))</a> <a id="3566" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3568" href="Exercises.Complexity.FiniteCSP.html#3289" class="Datatype">Rᵃ</a>
            <a id="3583" class="Symbol">}</a>


 <a id="3588" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3696" href="Exercises.Complexity.FiniteCSP.html#3696" class="Function">claim</a> <a id="3702" class="Symbol">:</a> <a id="3704" class="Symbol">(</a><a id="3705" href="Exercises.Complexity.FiniteCSP.html#3705" class="Bound">𝑩</a> <a id="3707" class="Symbol">:</a> <a id="3709" href="Structures.Basic.html#1565" class="Record">structure</a> <a id="3719" class="Symbol">{</a><a id="3720" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3722" class="Symbol">}{</a><a id="3724" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3726" class="Symbol">}{</a><a id="3728" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3730" class="Symbol">}{</a><a id="3732" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3734" class="Symbol">}</a> <a id="3736" href="Examples.Structures.Signatures.html#566" class="Function">S∅</a> <a id="3739" href="Examples.Structures.Signatures.html#894" class="Function">S001</a> <a id="3744" class="Symbol">{</a><a id="3745" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3747" class="Symbol">}{</a><a id="3749" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a><a id="3751" class="Symbol">})</a> <a id="3754" class="Symbol">→</a> <a id="3756" href="Structures.Homs.html#2728" class="Function">hom</a> <a id="3760" href="Exercises.Complexity.FiniteCSP.html#3705" class="Bound">𝑩</a> <a id="3762" href="Exercises.Complexity.FiniteCSP.html#3368" class="Function">𝑨</a>
 <a id="3765" href="Exercises.Complexity.FiniteCSP.html#3696" class="Function">claim</a> <a id="3771" href="Exercises.Complexity.FiniteCSP.html#3771" class="Bound">𝑩</a> <a id="3773" class="Symbol">=</a> <a id="3775" class="Symbol">(λ</a> <a id="3778" href="Exercises.Complexity.FiniteCSP.html#3778" class="Bound">x</a> <a id="3780" class="Symbol">→</a> <a id="3782" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a><a id="3785" class="Symbol">)</a> <a id="3787" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3789" class="Symbol">(λ</a> <a id="3792" href="Exercises.Complexity.FiniteCSP.html#3792" class="Bound">_</a> <a id="3794" href="Exercises.Complexity.FiniteCSP.html#3794" class="Bound">_</a> <a id="3796" href="Exercises.Complexity.FiniteCSP.html#3796" class="Bound">_</a> <a id="3798" class="Symbol">→</a> <a id="3800" href="Exercises.Complexity.FiniteCSP.html#3318" class="InductiveConstructor">r1</a><a id="3802" class="Symbol">)</a> <a id="3804" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3806" class="Symbol">λ</a> <a id="3808" class="Symbol">()</a>

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

<a id="4949" class="Keyword">module</a> <a id="solution-2-2"></a><a id="4956" href="Exercises.Complexity.FiniteCSP.html#4956" class="Module">solution-2-2</a> <a id="4969" class="Keyword">where</a>

 <a id="4977" class="Comment">-- The (purely) relational structure with</a>
 <a id="5020" class="Comment">-- + 2-element domain,</a>
 <a id="5044" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5095" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5151" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5156" href="Exercises.Complexity.FiniteCSP.html#5156" class="Datatype">Rᵃ</a> <a id="5159" class="Symbol">:</a> <a id="5161" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5166" class="Symbol">(</a><a id="5167" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="5169" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5171" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a><a id="5172" class="Symbol">)</a> <a id="5174" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a> <a id="5177" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5185" href="Exercises.Complexity.FiniteCSP.html#5185" class="InductiveConstructor">r1</a> <a id="5188" class="Symbol">:</a> <a id="5190" class="Symbol">(</a><a id="5191" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a> <a id="5195" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5197" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a> <a id="5201" class="Symbol">)</a> <a id="5203" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5205" href="Exercises.Complexity.FiniteCSP.html#5156" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5210" href="Exercises.Complexity.FiniteCSP.html#5210" class="InductiveConstructor">r2</a> <a id="5213" class="Symbol">:</a> <a id="5215" class="Symbol">(</a><a id="5216" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a> <a id="5220" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5222" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a> <a id="5226" class="Symbol">)</a> <a id="5228" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5230" href="Exercises.Complexity.FiniteCSP.html#5156" class="Datatype">Rᵃ</a>

 <a id="5235" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5240" href="Exercises.Complexity.FiniteCSP.html#5240" class="Datatype">C₀ᵃ</a> <a id="5244" class="Symbol">:</a> <a id="5246" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5251" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="5253" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a> <a id="5256" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5264" href="Exercises.Complexity.FiniteCSP.html#5264" class="InductiveConstructor">c₀</a> <a id="5267" class="Symbol">:</a> <a id="5269" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a> <a id="5273" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5275" href="Exercises.Complexity.FiniteCSP.html#5240" class="Datatype">C₀ᵃ</a>

 <a id="5281" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5286" href="Exercises.Complexity.FiniteCSP.html#5286" class="Datatype">C₁ᵃ</a> <a id="5290" class="Symbol">:</a> <a id="5292" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5297" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="5299" href="Exercises.Complexity.FiniteCSP.html#531" class="Primitive">ℓ₀</a> <a id="5302" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5310" href="Exercises.Complexity.FiniteCSP.html#5310" class="InductiveConstructor">c₁</a> <a id="5313" class="Symbol">:</a> <a id="5315" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a> <a id="5319" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5321" href="Exercises.Complexity.FiniteCSP.html#5286" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5328" href="Exercises.Complexity.FiniteCSP.html#5328" class="Function">𝑨</a> <a id="5330" class="Symbol">:</a> <a id="5332" href="Structures.Basic.html#1565" class="Record">structure</a> <a id="5342" href="Examples.Structures.Signatures.html#566" class="Function">S∅</a>    <a id="5348" class="Comment">-- (no operations)</a>
               <a id="5382" href="Examples.Structures.Signatures.html#1149" class="Function">S021</a>  <a id="5388" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5439" href="Exercises.Complexity.FiniteCSP.html#5328" class="Function">𝑨</a> <a id="5441" class="Symbol">=</a> <a id="5443" class="Keyword">record</a> <a id="5450" class="Symbol">{</a> <a id="5452" href="Structures.Basic.html#1717" class="Field">carrier</a> <a id="5460" class="Symbol">=</a> <a id="5462" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a>
            <a id="5476" class="Symbol">;</a> <a id="5478" href="Structures.Basic.html#1736" class="Field">op</a> <a id="5481" class="Symbol">=</a> <a id="5483" class="Symbol">λ</a> <a id="5485" class="Symbol">()</a>
            <a id="5500" class="Symbol">;</a> <a id="5502" href="Structures.Basic.html#1820" class="Field">rel</a> <a id="5506" class="Symbol">=</a> <a id="5508" href="Exercises.Complexity.FiniteCSP.html#5557" class="Function">rels</a>
            <a id="5525" class="Symbol">}</a>
            <a id="5539" class="Keyword">where</a>
            <a id="5557" href="Exercises.Complexity.FiniteCSP.html#5557" class="Function">rels</a> <a id="5562" class="Symbol">:</a> <a id="5564" class="Symbol">(</a><a id="5565" href="Exercises.Complexity.FiniteCSP.html#5565" class="Bound">r</a> <a id="5567" class="Symbol">:</a> <a id="5569" href="Overture.Preliminaries.html#3988" class="Datatype">𝟛</a><a id="5570" class="Symbol">)</a> <a id="5572" class="Symbol">→</a> <a id="5574" href="Relations.Continuous.html#3898" class="Function">Rel</a> <a id="5578" href="Overture.Preliminaries.html#3805" class="Datatype">𝟚</a> <a id="5580" class="Symbol">(</a><a id="5581" href="Structures.Basic.html#1310" class="Field">arity</a> <a id="5587" href="Examples.Structures.Signatures.html#1149" class="Function">S021</a> <a id="5592" href="Exercises.Complexity.FiniteCSP.html#5565" class="Bound">r</a><a id="5593" class="Symbol">)</a>
            <a id="5607" href="Exercises.Complexity.FiniteCSP.html#5557" class="Function">rels</a> <a id="5612" href="Overture.Preliminaries.html#4007" class="InductiveConstructor">𝟛.𝟎</a> <a id="5616" href="Exercises.Complexity.FiniteCSP.html#5616" class="Bound">x</a> <a id="5618" class="Symbol">=</a> <a id="5620" class="Symbol">((</a><a id="5622" href="Exercises.Complexity.FiniteCSP.html#5616" class="Bound">x</a> <a id="5624" href="Overture.Preliminaries.html#3855" class="InductiveConstructor">𝟚.𝟎</a><a id="5627" class="Symbol">)</a> <a id="5629" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5631" class="Symbol">(</a><a id="5632" href="Exercises.Complexity.FiniteCSP.html#5616" class="Bound">x</a> <a id="5634" href="Overture.Preliminaries.html#3906" class="InductiveConstructor">𝟚.𝟏</a><a id="5637" class="Symbol">))</a> <a id="5640" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5642" href="Exercises.Complexity.FiniteCSP.html#5156" class="Datatype">Rᵃ</a>
            <a id="5657" href="Exercises.Complexity.FiniteCSP.html#5557" class="Function">rels</a> <a id="5662" href="Overture.Preliminaries.html#4014" class="InductiveConstructor">𝟛.𝟏</a> <a id="5666" href="Exercises.Complexity.FiniteCSP.html#5666" class="Bound">x</a> <a id="5668" class="Symbol">=</a> <a id="5670" href="Exercises.Complexity.FiniteCSP.html#5666" class="Bound">x</a> <a id="5672" href="Overture.Preliminaries.html#3769" class="InductiveConstructor">𝟙.𝟎</a> <a id="5676" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5678" href="Exercises.Complexity.FiniteCSP.html#5240" class="Datatype">C₀ᵃ</a>
            <a id="5694" href="Exercises.Complexity.FiniteCSP.html#5557" class="Function">rels</a> <a id="5699" href="Overture.Preliminaries.html#4021" class="InductiveConstructor">𝟛.𝟐</a> <a id="5703" href="Exercises.Complexity.FiniteCSP.html#5703" class="Bound">x</a> <a id="5705" class="Symbol">=</a> <a id="5707" href="Exercises.Complexity.FiniteCSP.html#5703" class="Bound">x</a> <a id="5709" href="Overture.Preliminaries.html#3769" class="InductiveConstructor">𝟙.𝟎</a> <a id="5713" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5715" href="Exercises.Complexity.FiniteCSP.html#5286" class="Datatype">C₁ᵃ</a>


 <a id="5722" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5826" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5872" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5908" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="5979" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6057" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6137" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6185" class="Comment">--          )</a>
 <a id="6200" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6221" class="Comment">-- claim 𝑩 x = {!!}</a>

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



