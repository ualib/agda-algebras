---
layout: default
title : "Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team and Libor Barto"
---

### <a id="csp-exercises">CSP Exercises</a>

This is the [Exercises.Complexity.FiniteCSP][] module of the [Agda Universal Algebra Library][].

Excercises in this module were created by Libor Barto for students at Charles
University in Prague. They were formalized in dependent type theory by the
[agda-algebras development team][].

<pre class="Agda">

<a id="535" class="Symbol">{-#</a> <a id="539" class="Keyword">OPTIONS</a> <a id="547" class="Pragma">--without-K</a> <a id="559" class="Pragma">--exact-split</a> <a id="573" class="Pragma">--safe</a> <a id="580" class="Symbol">#-}</a>

<a id="585" class="Keyword">module</a> <a id="592" href="Exercises.Complexity.FiniteCSP.html" class="Module">Exercises.Complexity.FiniteCSP</a>  <a id="624" class="Keyword">where</a>

<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="659" class="Keyword">using</a> <a id="665" class="Symbol">(</a> <a id="667" class="Symbol">)</a> <a id="669" class="Keyword">renaming</a> <a id="678" class="Symbol">(</a><a id="679" href="Agda.Primitive.html#915" class="Primitive">lzero</a> <a id="685" class="Symbol">to</a> <a id="688" class="Primitive">ℓ₀</a> <a id="691" class="Symbol">)</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="Data.Product.html" class="Module">Data.Product</a>    <a id="721" class="Keyword">using</a> <a id="727" class="Symbol">(</a> <a id="729" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">_,_</a> <a id="733" class="Symbol">;</a> <a id="735" href="Data.Product.Base.html#1618" class="Function Operator">_×_</a> <a id="739" class="Symbol">)</a>
<a id="741" class="Keyword">open</a> <a id="746" class="Keyword">import</a> <a id="753" href="Data.Unit.Base.html" class="Module">Data.Unit.Base</a>  <a id="769" class="Keyword">using</a> <a id="775" class="Symbol">()</a> <a id="778" class="Keyword">renaming</a> <a id="787" class="Symbol">(</a> <a id="789" href="Agda.Builtin.Unit.html#212" class="InductiveConstructor">tt</a> <a id="792" class="Symbol">to</a> <a id="795" class="InductiveConstructor">𝟎</a> <a id="797" class="Symbol">)</a>
<a id="799" class="Keyword">open</a> <a id="804" class="Keyword">import</a> <a id="811" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="827" class="Keyword">using</a> <a id="833" class="Symbol">(</a> <a id="835" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="840" class="Symbol">;</a> <a id="842" href="Relation.Unary.html#1818" class="Function Operator">_∈_</a> <a id="846" class="Symbol">)</a>

<a id="849" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="942" class="Keyword">open</a> <a id="947" class="Keyword">import</a> <a id="954" href="Overture.Basic.html" class="Module">Overture.Basic</a>                  <a id="986" class="Keyword">using</a> <a id="992" class="Symbol">(</a> <a id="994" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="996" class="Symbol">;</a> <a id="998" href="Overture.Basic.html#3788" class="Datatype">𝟛</a> <a id="1000" class="Symbol">)</a>
<a id="1002" class="Keyword">open</a> <a id="1007" class="Keyword">import</a> <a id="1014" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>       <a id="1046" class="Keyword">using</a> <a id="1052" class="Symbol">(</a> <a id="1054" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="1058" class="Symbol">)</a>
<a id="1060" class="Keyword">open</a> <a id="1065" class="Keyword">import</a> <a id="1072" href="Base.Structures.Basic.html" class="Module">Base.Structures.Basic</a>           <a id="1104" class="Keyword">using</a> <a id="1110" class="Symbol">(</a> <a id="1112" href="Base.Structures.Basic.html#1233" class="Record">signature</a> <a id="1122" class="Symbol">;</a> <a id="1124" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="1134" class="Symbol">)</a>
<a id="1136" class="Keyword">open</a> <a id="1141" class="Keyword">import</a> <a id="1148" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a>  <a id="1180" class="Keyword">using</a> <a id="1186" class="Symbol">(</a> <a id="1188" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a> <a id="1191" class="Symbol">;</a> <a id="1193" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a> <a id="1198" class="Symbol">;</a> <a id="1200" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a><a id="1204" class="Symbol">)</a>
<a id="1206" class="Keyword">open</a> <a id="1211" class="Keyword">import</a> <a id="1218" href="Base.Structures.Homs.html" class="Module">Base.Structures.Homs</a>            <a id="1250" class="Keyword">using</a> <a id="1256" class="Symbol">(</a> <a id="1258" href="Base.Structures.Homs.html#2703" class="Function">hom</a> <a id="1262" class="Symbol">)</a>
<a id="1264" class="Keyword">open</a> <a id="1269" href="Base.Structures.Basic.html#1233" class="Module">signature</a>
<a id="1279" class="Keyword">open</a> <a id="1284" href="Base.Structures.Basic.html#1566" class="Module">structure</a>

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
<a id="3334" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3341" href="Exercises.Complexity.FiniteCSP.html#3341" class="Module">solution-2-1</a> <a id="3354" class="Keyword">where</a>

 <a id="3362" class="Comment">-- The (purely) relational structure with</a>
 <a id="3405" class="Comment">-- + 2-element domain,</a>
 <a id="3429" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3480" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3485" href="Exercises.Complexity.FiniteCSP.html#3485" class="Datatype">Rᵃ</a> <a id="3488" class="Symbol">:</a> <a id="3490" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="3495" class="Symbol">(</a><a id="3496" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="3498" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="3500" href="Overture.Basic.html#3723" class="Datatype">𝟚</a><a id="3501" class="Symbol">)</a> <a id="3503" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a> <a id="3506" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3514" href="Exercises.Complexity.FiniteCSP.html#3514" class="InductiveConstructor">r1</a> <a id="3517" class="Symbol">:</a> <a id="3519" class="Symbol">(</a><a id="3520" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a> <a id="3524" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="3526" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a> <a id="3530" class="Symbol">)</a> <a id="3532" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="3534" href="Exercises.Complexity.FiniteCSP.html#3485" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3539" href="Exercises.Complexity.FiniteCSP.html#3539" class="InductiveConstructor">r2</a> <a id="3542" class="Symbol">:</a> <a id="3544" class="Symbol">(</a><a id="3545" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a> <a id="3549" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="3551" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a> <a id="3555" class="Symbol">)</a> <a id="3557" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="3559" href="Exercises.Complexity.FiniteCSP.html#3485" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3564" href="Exercises.Complexity.FiniteCSP.html#3564" class="Function">𝑨</a> <a id="3566" class="Symbol">:</a> <a id="3568" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="3578" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a>    <a id="3584" class="Comment">-- (no operation symbols)</a>
               <a id="3625" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a>  <a id="3631" class="Comment">-- (one binary relation symbol)</a>

 <a id="3665" href="Exercises.Complexity.FiniteCSP.html#3564" class="Function">𝑨</a> <a id="3667" class="Symbol">=</a> <a id="3669" class="Keyword">record</a> <a id="3676" class="Symbol">{</a> <a id="3678" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="3686" class="Symbol">=</a> <a id="3688" href="Overture.Basic.html#3723" class="Datatype">𝟚</a>
            <a id="3702" class="Symbol">;</a> <a id="3704" href="Base.Structures.Basic.html#1749" class="Field">op</a> <a id="3707" class="Symbol">=</a> <a id="3709" class="Symbol">λ</a> <a id="3711" class="Symbol">()</a>
            <a id="3726" class="Symbol">;</a> <a id="3728" href="Base.Structures.Basic.html#1833" class="Field">rel</a> <a id="3732" class="Symbol">=</a> <a id="3734" class="Symbol">λ</a> <a id="3736" href="Exercises.Complexity.FiniteCSP.html#3736" class="Bound">_</a> <a id="3738" href="Exercises.Complexity.FiniteCSP.html#3738" class="Bound">x</a> <a id="3740" class="Symbol">→</a> <a id="3742" class="Symbol">((</a><a id="3744" href="Exercises.Complexity.FiniteCSP.html#3738" class="Bound">x</a> <a id="3746" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a><a id="3749" class="Symbol">)</a> <a id="3751" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="3753" class="Symbol">(</a><a id="3754" href="Exercises.Complexity.FiniteCSP.html#3738" class="Bound">x</a> <a id="3756" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a><a id="3759" class="Symbol">))</a> <a id="3762" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="3764" href="Exercises.Complexity.FiniteCSP.html#3485" class="Datatype">Rᵃ</a>
            <a id="3779" class="Symbol">}</a>


 <a id="3784" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3892" href="Exercises.Complexity.FiniteCSP.html#3892" class="Function">claim</a> <a id="3898" class="Symbol">:</a> <a id="3900" class="Symbol">(</a><a id="3901" href="Exercises.Complexity.FiniteCSP.html#3901" class="Bound">𝑩</a> <a id="3903" class="Symbol">:</a> <a id="3905" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="3915" class="Symbol">{</a><a id="3916" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3918" class="Symbol">}{</a><a id="3920" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3922" class="Symbol">}{</a><a id="3924" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3926" class="Symbol">}{</a><a id="3928" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3930" class="Symbol">}</a> <a id="3932" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a> <a id="3935" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a> <a id="3940" class="Symbol">{</a><a id="3941" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3943" class="Symbol">}{</a><a id="3945" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a><a id="3947" class="Symbol">})</a> <a id="3950" class="Symbol">→</a> <a id="3952" href="Base.Structures.Homs.html#2703" class="Function">hom</a> <a id="3956" href="Exercises.Complexity.FiniteCSP.html#3901" class="Bound">𝑩</a> <a id="3958" href="Exercises.Complexity.FiniteCSP.html#3564" class="Function">𝑨</a>
 <a id="3961" href="Exercises.Complexity.FiniteCSP.html#3892" class="Function">claim</a> <a id="3967" href="Exercises.Complexity.FiniteCSP.html#3967" class="Bound">𝑩</a> <a id="3969" class="Symbol">=</a> <a id="3971" class="Symbol">(λ</a> <a id="3974" href="Exercises.Complexity.FiniteCSP.html#3974" class="Bound">x</a> <a id="3976" class="Symbol">→</a> <a id="3978" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a><a id="3981" class="Symbol">)</a> <a id="3983" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="3985" class="Symbol">(λ</a> <a id="3988" href="Exercises.Complexity.FiniteCSP.html#3988" class="Bound">_</a> <a id="3990" href="Exercises.Complexity.FiniteCSP.html#3990" class="Bound">_</a> <a id="3992" href="Exercises.Complexity.FiniteCSP.html#3992" class="Bound">_</a> <a id="3994" class="Symbol">→</a> <a id="3996" href="Exercises.Complexity.FiniteCSP.html#3514" class="InductiveConstructor">r1</a><a id="3998" class="Symbol">)</a> <a id="4000" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="4002" class="Symbol">λ</a> <a id="4004" class="Symbol">()</a>

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

<a id="5145" class="Keyword">module</a> <a id="solution-2-2"></a><a id="5152" href="Exercises.Complexity.FiniteCSP.html#5152" class="Module">solution-2-2</a> <a id="5165" class="Keyword">where</a>

 <a id="5173" class="Comment">-- The (purely) relational structure with</a>
 <a id="5216" class="Comment">-- + 2-element domain,</a>
 <a id="5240" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5291" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5347" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5352" href="Exercises.Complexity.FiniteCSP.html#5352" class="Datatype">Rᵃ</a> <a id="5355" class="Symbol">:</a> <a id="5357" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="5362" class="Symbol">(</a><a id="5363" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="5365" href="Data.Product.Base.html#1618" class="Function Operator">×</a> <a id="5367" href="Overture.Basic.html#3723" class="Datatype">𝟚</a><a id="5368" class="Symbol">)</a> <a id="5370" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a> <a id="5373" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5381" href="Exercises.Complexity.FiniteCSP.html#5381" class="InductiveConstructor">r1</a> <a id="5384" class="Symbol">:</a> <a id="5386" class="Symbol">(</a><a id="5387" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a> <a id="5391" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5393" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a> <a id="5397" class="Symbol">)</a> <a id="5399" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5401" href="Exercises.Complexity.FiniteCSP.html#5352" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5406" href="Exercises.Complexity.FiniteCSP.html#5406" class="InductiveConstructor">r2</a> <a id="5409" class="Symbol">:</a> <a id="5411" class="Symbol">(</a><a id="5412" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a> <a id="5416" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5418" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a> <a id="5422" class="Symbol">)</a> <a id="5424" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5426" href="Exercises.Complexity.FiniteCSP.html#5352" class="Datatype">Rᵃ</a>

 <a id="5431" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5436" href="Exercises.Complexity.FiniteCSP.html#5436" class="Datatype">C₀ᵃ</a> <a id="5440" class="Symbol">:</a> <a id="5442" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="5447" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="5449" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a> <a id="5452" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5460" href="Exercises.Complexity.FiniteCSP.html#5460" class="InductiveConstructor">c₀</a> <a id="5463" class="Symbol">:</a> <a id="5465" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a> <a id="5469" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5471" href="Exercises.Complexity.FiniteCSP.html#5436" class="Datatype">C₀ᵃ</a>

 <a id="5477" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5482" href="Exercises.Complexity.FiniteCSP.html#5482" class="Datatype">C₁ᵃ</a> <a id="5486" class="Symbol">:</a> <a id="5488" href="Relation.Unary.html#1178" class="Function">Pred</a> <a id="5493" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="5495" href="Exercises.Complexity.FiniteCSP.html#688" class="Primitive">ℓ₀</a> <a id="5498" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5506" href="Exercises.Complexity.FiniteCSP.html#5506" class="InductiveConstructor">c₁</a> <a id="5509" class="Symbol">:</a> <a id="5511" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a> <a id="5515" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5517" href="Exercises.Complexity.FiniteCSP.html#5482" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5524" href="Exercises.Complexity.FiniteCSP.html#5524" class="Function">𝑨</a> <a id="5526" class="Symbol">:</a> <a id="5528" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="5538" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a>    <a id="5544" class="Comment">-- (no operations)</a>
               <a id="5578" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a>  <a id="5584" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5635" href="Exercises.Complexity.FiniteCSP.html#5524" class="Function">𝑨</a> <a id="5637" class="Symbol">=</a> <a id="5639" class="Keyword">record</a> <a id="5646" class="Symbol">{</a> <a id="5648" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="5656" class="Symbol">=</a> <a id="5658" href="Overture.Basic.html#3723" class="Datatype">𝟚</a>
            <a id="5672" class="Symbol">;</a> <a id="5674" href="Base.Structures.Basic.html#1749" class="Field">op</a> <a id="5677" class="Symbol">=</a> <a id="5679" class="Symbol">λ</a> <a id="5681" class="Symbol">()</a>
            <a id="5696" class="Symbol">;</a> <a id="5698" href="Base.Structures.Basic.html#1833" class="Field">rel</a> <a id="5702" class="Symbol">=</a> <a id="5704" href="Exercises.Complexity.FiniteCSP.html#5753" class="Function">rels</a>
            <a id="5721" class="Symbol">}</a>
            <a id="5735" class="Keyword">where</a>
            <a id="5753" href="Exercises.Complexity.FiniteCSP.html#5753" class="Function">rels</a> <a id="5758" class="Symbol">:</a> <a id="5760" class="Symbol">(</a><a id="5761" href="Exercises.Complexity.FiniteCSP.html#5761" class="Bound">r</a> <a id="5763" class="Symbol">:</a> <a id="5765" href="Overture.Basic.html#3788" class="Datatype">𝟛</a><a id="5766" class="Symbol">)</a> <a id="5768" class="Symbol">→</a> <a id="5770" href="Base.Relations.Continuous.html#4456" class="Function">Rel</a> <a id="5774" href="Overture.Basic.html#3723" class="Datatype">𝟚</a> <a id="5776" class="Symbol">(</a><a id="5777" href="Base.Structures.Basic.html#1311" class="Field">arity</a> <a id="5783" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a> <a id="5788" href="Exercises.Complexity.FiniteCSP.html#5761" class="Bound">r</a><a id="5789" class="Symbol">)</a>
            <a id="5803" href="Exercises.Complexity.FiniteCSP.html#5753" class="Function">rels</a> <a id="5808" href="Overture.Basic.html#3806" class="InductiveConstructor">𝟛.𝟎</a> <a id="5812" href="Exercises.Complexity.FiniteCSP.html#5812" class="Bound">x</a> <a id="5814" class="Symbol">=</a> <a id="5816" class="Symbol">((</a><a id="5818" href="Exercises.Complexity.FiniteCSP.html#5812" class="Bound">x</a> <a id="5820" href="Overture.Basic.html#3741" class="InductiveConstructor">𝟚.𝟎</a><a id="5823" class="Symbol">)</a> <a id="5825" href="Agda.Builtin.Sigma.html#235" class="InductiveConstructor Operator">,</a> <a id="5827" class="Symbol">(</a><a id="5828" href="Exercises.Complexity.FiniteCSP.html#5812" class="Bound">x</a> <a id="5830" href="Overture.Basic.html#3750" class="InductiveConstructor">𝟚.𝟏</a><a id="5833" class="Symbol">))</a> <a id="5836" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5838" href="Exercises.Complexity.FiniteCSP.html#5352" class="Datatype">Rᵃ</a>
            <a id="5853" href="Exercises.Complexity.FiniteCSP.html#5753" class="Function">rels</a> <a id="5858" href="Overture.Basic.html#3815" class="InductiveConstructor">𝟛.𝟏</a> <a id="5862" href="Exercises.Complexity.FiniteCSP.html#5862" class="Bound">x</a> <a id="5864" class="Symbol">=</a> <a id="5866" href="Exercises.Complexity.FiniteCSP.html#5862" class="Bound">x</a> <a id="5868" href="Exercises.Complexity.FiniteCSP.html#795" class="InductiveConstructor">𝟎</a> <a id="5870" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5872" href="Exercises.Complexity.FiniteCSP.html#5436" class="Datatype">C₀ᵃ</a>
            <a id="5888" href="Exercises.Complexity.FiniteCSP.html#5753" class="Function">rels</a> <a id="5893" href="Overture.Basic.html#3824" class="InductiveConstructor">𝟛.𝟐</a> <a id="5897" href="Exercises.Complexity.FiniteCSP.html#5897" class="Bound">x</a> <a id="5899" class="Symbol">=</a> <a id="5901" href="Exercises.Complexity.FiniteCSP.html#5897" class="Bound">x</a> <a id="5903" href="Exercises.Complexity.FiniteCSP.html#795" class="InductiveConstructor">𝟎</a> <a id="5905" href="Relation.Unary.html#1818" class="Function Operator">∈</a> <a id="5907" href="Exercises.Complexity.FiniteCSP.html#5482" class="Datatype">C₁ᵃ</a>


 <a id="5914" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="6018" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="6064" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="6100" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6171" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6249" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6329" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6377" class="Comment">--          )</a>
 <a id="6392" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6413" class="Comment">-- claim 𝑩 x = {!!}</a>

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


