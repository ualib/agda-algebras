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
<a id="822" class="Keyword">open</a> <a id="827" class="Keyword">import</a> <a id="834" href="Overture.Basic.html" class="Module">Overture.Basic</a>                  <a id="866" class="Keyword">using</a> <a id="872" class="Symbol">(</a> <a id="874" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="876" class="Symbol">;</a> <a id="878" href="Overture.Basic.html#3765" class="Datatype">𝟛</a> <a id="880" class="Symbol">)</a>
<a id="882" class="Keyword">open</a> <a id="887" class="Keyword">import</a> <a id="894" href="Base.Relations.Continuous.html" class="Module">Base.Relations.Continuous</a>       <a id="926" class="Keyword">using</a> <a id="932" class="Symbol">(</a> <a id="934" href="Base.Relations.Continuous.html#4452" class="Function">Rel</a> <a id="938" class="Symbol">)</a>
<a id="940" class="Keyword">open</a> <a id="945" class="Keyword">import</a> <a id="952" href="Base.Structures.Basic.html" class="Module">Base.Structures.Basic</a>           <a id="984" class="Keyword">using</a> <a id="990" class="Symbol">(</a> <a id="992" href="Base.Structures.Basic.html#1233" class="Record">signature</a> <a id="1002" class="Symbol">;</a> <a id="1004" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="1014" class="Symbol">)</a>
<a id="1016" class="Keyword">open</a> <a id="1021" class="Keyword">import</a> <a id="1028" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a>  <a id="1060" class="Keyword">using</a> <a id="1066" class="Symbol">(</a> <a id="1068" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a> <a id="1071" class="Symbol">;</a> <a id="1073" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a> <a id="1078" class="Symbol">;</a> <a id="1080" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a><a id="1084" class="Symbol">)</a>
<a id="1086" class="Keyword">open</a> <a id="1091" class="Keyword">import</a> <a id="1098" href="Base.Structures.Homs.html" class="Module">Base.Structures.Homs</a>            <a id="1130" class="Keyword">using</a> <a id="1136" class="Symbol">(</a> <a id="1138" href="Base.Structures.Homs.html#2703" class="Function">hom</a> <a id="1142" class="Symbol">)</a>
<a id="1144" class="Keyword">open</a> <a id="1149" href="Base.Structures.Basic.html#1233" class="Module">signature</a>
<a id="1159" class="Keyword">open</a> <a id="1164" href="Base.Structures.Basic.html#1566" class="Module">structure</a>

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
<a id="3214" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3221" href="Exercises.Complexity.FiniteCSP.html#3221" class="Module">solution-2-1</a> <a id="3234" class="Keyword">where</a>

 <a id="3242" class="Comment">-- The (purely) relational structure with</a>
 <a id="3285" class="Comment">-- + 2-element domain,</a>
 <a id="3309" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3360" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3365" href="Exercises.Complexity.FiniteCSP.html#3365" class="Datatype">Rᵃ</a> <a id="3368" class="Symbol">:</a> <a id="3370" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3375" class="Symbol">(</a><a id="3376" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="3378" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3380" href="Overture.Basic.html#3700" class="Datatype">𝟚</a><a id="3381" class="Symbol">)</a> <a id="3383" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="3386" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3394" href="Exercises.Complexity.FiniteCSP.html#3394" class="InductiveConstructor">r1</a> <a id="3397" class="Symbol">:</a> <a id="3399" class="Symbol">(</a><a id="3400" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a> <a id="3404" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3406" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a> <a id="3410" class="Symbol">)</a> <a id="3412" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3414" href="Exercises.Complexity.FiniteCSP.html#3365" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3419" href="Exercises.Complexity.FiniteCSP.html#3419" class="InductiveConstructor">r2</a> <a id="3422" class="Symbol">:</a> <a id="3424" class="Symbol">(</a><a id="3425" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a> <a id="3429" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3431" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a> <a id="3435" class="Symbol">)</a> <a id="3437" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3439" href="Exercises.Complexity.FiniteCSP.html#3365" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3444" href="Exercises.Complexity.FiniteCSP.html#3444" class="Function">𝑨</a> <a id="3446" class="Symbol">:</a> <a id="3448" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="3458" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a>    <a id="3464" class="Comment">-- (no operation symbols)</a>
               <a id="3505" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a>  <a id="3511" class="Comment">-- (one binary relation symbol)</a>

 <a id="3545" href="Exercises.Complexity.FiniteCSP.html#3444" class="Function">𝑨</a> <a id="3547" class="Symbol">=</a> <a id="3549" class="Keyword">record</a> <a id="3556" class="Symbol">{</a> <a id="3558" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="3566" class="Symbol">=</a> <a id="3568" href="Overture.Basic.html#3700" class="Datatype">𝟚</a>
            <a id="3582" class="Symbol">;</a> <a id="3584" href="Base.Structures.Basic.html#1749" class="Field">op</a> <a id="3587" class="Symbol">=</a> <a id="3589" class="Symbol">λ</a> <a id="3591" class="Symbol">()</a>
            <a id="3606" class="Symbol">;</a> <a id="3608" href="Base.Structures.Basic.html#1833" class="Field">rel</a> <a id="3612" class="Symbol">=</a> <a id="3614" class="Symbol">λ</a> <a id="3616" href="Exercises.Complexity.FiniteCSP.html#3616" class="Bound">_</a> <a id="3618" href="Exercises.Complexity.FiniteCSP.html#3618" class="Bound">x</a> <a id="3620" class="Symbol">→</a> <a id="3622" class="Symbol">((</a><a id="3624" href="Exercises.Complexity.FiniteCSP.html#3618" class="Bound">x</a> <a id="3626" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a><a id="3629" class="Symbol">)</a> <a id="3631" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3633" class="Symbol">(</a><a id="3634" href="Exercises.Complexity.FiniteCSP.html#3618" class="Bound">x</a> <a id="3636" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a><a id="3639" class="Symbol">))</a> <a id="3642" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3644" href="Exercises.Complexity.FiniteCSP.html#3365" class="Datatype">Rᵃ</a>
            <a id="3659" class="Symbol">}</a>


 <a id="3664" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3772" href="Exercises.Complexity.FiniteCSP.html#3772" class="Function">claim</a> <a id="3778" class="Symbol">:</a> <a id="3780" class="Symbol">(</a><a id="3781" href="Exercises.Complexity.FiniteCSP.html#3781" class="Bound">𝑩</a> <a id="3783" class="Symbol">:</a> <a id="3785" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="3795" class="Symbol">{</a><a id="3796" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3798" class="Symbol">}{</a><a id="3800" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3802" class="Symbol">}{</a><a id="3804" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3806" class="Symbol">}{</a><a id="3808" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3810" class="Symbol">}</a> <a id="3812" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a> <a id="3815" href="Examples.Structures.Signatures.html#1093" class="Function">S001</a> <a id="3820" class="Symbol">{</a><a id="3821" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3823" class="Symbol">}{</a><a id="3825" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a><a id="3827" class="Symbol">})</a> <a id="3830" class="Symbol">→</a> <a id="3832" href="Base.Structures.Homs.html#2703" class="Function">hom</a> <a id="3836" href="Exercises.Complexity.FiniteCSP.html#3781" class="Bound">𝑩</a> <a id="3838" href="Exercises.Complexity.FiniteCSP.html#3444" class="Function">𝑨</a>
 <a id="3841" href="Exercises.Complexity.FiniteCSP.html#3772" class="Function">claim</a> <a id="3847" href="Exercises.Complexity.FiniteCSP.html#3847" class="Bound">𝑩</a> <a id="3849" class="Symbol">=</a> <a id="3851" class="Symbol">(λ</a> <a id="3854" href="Exercises.Complexity.FiniteCSP.html#3854" class="Bound">x</a> <a id="3856" class="Symbol">→</a> <a id="3858" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a><a id="3861" class="Symbol">)</a> <a id="3863" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3865" class="Symbol">(λ</a> <a id="3868" href="Exercises.Complexity.FiniteCSP.html#3868" class="Bound">_</a> <a id="3870" href="Exercises.Complexity.FiniteCSP.html#3870" class="Bound">_</a> <a id="3872" href="Exercises.Complexity.FiniteCSP.html#3872" class="Bound">_</a> <a id="3874" class="Symbol">→</a> <a id="3876" href="Exercises.Complexity.FiniteCSP.html#3394" class="InductiveConstructor">r1</a><a id="3878" class="Symbol">)</a> <a id="3880" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3882" class="Symbol">λ</a> <a id="3884" class="Symbol">()</a>

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

<a id="5025" class="Keyword">module</a> <a id="solution-2-2"></a><a id="5032" href="Exercises.Complexity.FiniteCSP.html#5032" class="Module">solution-2-2</a> <a id="5045" class="Keyword">where</a>

 <a id="5053" class="Comment">-- The (purely) relational structure with</a>
 <a id="5096" class="Comment">-- + 2-element domain,</a>
 <a id="5120" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5171" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5227" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5232" href="Exercises.Complexity.FiniteCSP.html#5232" class="Datatype">Rᵃ</a> <a id="5235" class="Symbol">:</a> <a id="5237" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5242" class="Symbol">(</a><a id="5243" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="5245" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5247" href="Overture.Basic.html#3700" class="Datatype">𝟚</a><a id="5248" class="Symbol">)</a> <a id="5250" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5253" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5261" href="Exercises.Complexity.FiniteCSP.html#5261" class="InductiveConstructor">r1</a> <a id="5264" class="Symbol">:</a> <a id="5266" class="Symbol">(</a><a id="5267" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a> <a id="5271" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5273" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a> <a id="5277" class="Symbol">)</a> <a id="5279" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5281" href="Exercises.Complexity.FiniteCSP.html#5232" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5286" href="Exercises.Complexity.FiniteCSP.html#5286" class="InductiveConstructor">r2</a> <a id="5289" class="Symbol">:</a> <a id="5291" class="Symbol">(</a><a id="5292" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a> <a id="5296" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5298" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a> <a id="5302" class="Symbol">)</a> <a id="5304" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5306" href="Exercises.Complexity.FiniteCSP.html#5232" class="Datatype">Rᵃ</a>

 <a id="5311" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5316" href="Exercises.Complexity.FiniteCSP.html#5316" class="Datatype">C₀ᵃ</a> <a id="5320" class="Symbol">:</a> <a id="5322" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5327" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="5329" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5332" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5340" href="Exercises.Complexity.FiniteCSP.html#5340" class="InductiveConstructor">c₀</a> <a id="5343" class="Symbol">:</a> <a id="5345" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a> <a id="5349" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5351" href="Exercises.Complexity.FiniteCSP.html#5316" class="Datatype">C₀ᵃ</a>

 <a id="5357" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5362" href="Exercises.Complexity.FiniteCSP.html#5362" class="Datatype">C₁ᵃ</a> <a id="5366" class="Symbol">:</a> <a id="5368" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5373" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="5375" href="Exercises.Complexity.FiniteCSP.html#568" class="Primitive">ℓ₀</a> <a id="5378" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5386" href="Exercises.Complexity.FiniteCSP.html#5386" class="InductiveConstructor">c₁</a> <a id="5389" class="Symbol">:</a> <a id="5391" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a> <a id="5395" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5397" href="Exercises.Complexity.FiniteCSP.html#5362" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5404" href="Exercises.Complexity.FiniteCSP.html#5404" class="Function">𝑨</a> <a id="5406" class="Symbol">:</a> <a id="5408" href="Base.Structures.Basic.html#1566" class="Record">structure</a> <a id="5418" href="Examples.Structures.Signatures.html#765" class="Function">S∅</a>    <a id="5424" class="Comment">-- (no operations)</a>
               <a id="5458" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a>  <a id="5464" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5515" href="Exercises.Complexity.FiniteCSP.html#5404" class="Function">𝑨</a> <a id="5517" class="Symbol">=</a> <a id="5519" class="Keyword">record</a> <a id="5526" class="Symbol">{</a> <a id="5528" href="Base.Structures.Basic.html#1730" class="Field">carrier</a> <a id="5536" class="Symbol">=</a> <a id="5538" href="Overture.Basic.html#3700" class="Datatype">𝟚</a>
            <a id="5552" class="Symbol">;</a> <a id="5554" href="Base.Structures.Basic.html#1749" class="Field">op</a> <a id="5557" class="Symbol">=</a> <a id="5559" class="Symbol">λ</a> <a id="5561" class="Symbol">()</a>
            <a id="5576" class="Symbol">;</a> <a id="5578" href="Base.Structures.Basic.html#1833" class="Field">rel</a> <a id="5582" class="Symbol">=</a> <a id="5584" href="Exercises.Complexity.FiniteCSP.html#5633" class="Function">rels</a>
            <a id="5601" class="Symbol">}</a>
            <a id="5615" class="Keyword">where</a>
            <a id="5633" href="Exercises.Complexity.FiniteCSP.html#5633" class="Function">rels</a> <a id="5638" class="Symbol">:</a> <a id="5640" class="Symbol">(</a><a id="5641" href="Exercises.Complexity.FiniteCSP.html#5641" class="Bound">r</a> <a id="5643" class="Symbol">:</a> <a id="5645" href="Overture.Basic.html#3765" class="Datatype">𝟛</a><a id="5646" class="Symbol">)</a> <a id="5648" class="Symbol">→</a> <a id="5650" href="Base.Relations.Continuous.html#4452" class="Function">Rel</a> <a id="5654" href="Overture.Basic.html#3700" class="Datatype">𝟚</a> <a id="5656" class="Symbol">(</a><a id="5657" href="Base.Structures.Basic.html#1311" class="Field">arity</a> <a id="5663" href="Examples.Structures.Signatures.html#1348" class="Function">S021</a> <a id="5668" href="Exercises.Complexity.FiniteCSP.html#5641" class="Bound">r</a><a id="5669" class="Symbol">)</a>
            <a id="5683" href="Exercises.Complexity.FiniteCSP.html#5633" class="Function">rels</a> <a id="5688" href="Overture.Basic.html#3783" class="InductiveConstructor">𝟛.𝟎</a> <a id="5692" href="Exercises.Complexity.FiniteCSP.html#5692" class="Bound">x</a> <a id="5694" class="Symbol">=</a> <a id="5696" class="Symbol">((</a><a id="5698" href="Exercises.Complexity.FiniteCSP.html#5692" class="Bound">x</a> <a id="5700" href="Overture.Basic.html#3718" class="InductiveConstructor">𝟚.𝟎</a><a id="5703" class="Symbol">)</a> <a id="5705" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5707" class="Symbol">(</a><a id="5708" href="Exercises.Complexity.FiniteCSP.html#5692" class="Bound">x</a> <a id="5710" href="Overture.Basic.html#3727" class="InductiveConstructor">𝟚.𝟏</a><a id="5713" class="Symbol">))</a> <a id="5716" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5718" href="Exercises.Complexity.FiniteCSP.html#5232" class="Datatype">Rᵃ</a>
            <a id="5733" href="Exercises.Complexity.FiniteCSP.html#5633" class="Function">rels</a> <a id="5738" href="Overture.Basic.html#3792" class="InductiveConstructor">𝟛.𝟏</a> <a id="5742" href="Exercises.Complexity.FiniteCSP.html#5742" class="Bound">x</a> <a id="5744" class="Symbol">=</a> <a id="5746" href="Exercises.Complexity.FiniteCSP.html#5742" class="Bound">x</a> <a id="5748" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5750" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5752" href="Exercises.Complexity.FiniteCSP.html#5316" class="Datatype">C₀ᵃ</a>
            <a id="5768" href="Exercises.Complexity.FiniteCSP.html#5633" class="Function">rels</a> <a id="5773" href="Overture.Basic.html#3801" class="InductiveConstructor">𝟛.𝟐</a> <a id="5777" href="Exercises.Complexity.FiniteCSP.html#5777" class="Bound">x</a> <a id="5779" class="Symbol">=</a> <a id="5781" href="Exercises.Complexity.FiniteCSP.html#5777" class="Bound">x</a> <a id="5783" href="Exercises.Complexity.FiniteCSP.html#675" class="InductiveConstructor">𝟎</a> <a id="5785" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5787" href="Exercises.Complexity.FiniteCSP.html#5362" class="Datatype">C₁ᵃ</a>


 <a id="5794" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5898" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5944" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5980" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6051" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6129" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6209" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6257" class="Comment">--          )</a>
 <a id="6272" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6293" class="Comment">-- claim 𝑩 x = {!!}</a>

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


