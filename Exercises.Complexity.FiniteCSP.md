---
layout: default
title : "Exercises.Complexity.FiniteCSP module (The Agda Universal Algebra Library)"
date : "2021-07-26"
author: "agda-algebras development team][] and Libor Bar"
---

All excercises in this module were created by Libor Barto for students at Charles University in Prague. They were formalized in dependent type theory by the [agda-algebras development team][].

### CSP Exercises

<pre class="Agda">

<a id="416" class="Symbol">{-#</a> <a id="420" class="Keyword">OPTIONS</a> <a id="428" class="Pragma">--without-K</a> <a id="440" class="Pragma">--exact-split</a> <a id="454" class="Pragma">--safe</a> <a id="461" class="Symbol">#-}</a>

<a id="466" class="Keyword">module</a> <a id="473" href="Exercises.Complexity.FiniteCSP.html" class="Module">Exercises.Complexity.FiniteCSP</a>  <a id="505" class="Keyword">where</a>

<a id="512" class="Keyword">open</a> <a id="517" class="Keyword">import</a> <a id="524" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>  <a id="540" class="Keyword">using</a> <a id="546" class="Symbol">(</a> <a id="548" class="Symbol">)</a> <a id="550" class="Keyword">renaming</a> <a id="559" class="Symbol">(</a><a id="560" href="Agda.Primitive.html#764" class="Primitive">lzero</a> <a id="566" class="Symbol">to</a> <a id="569" class="Primitive">ℓ₀</a> <a id="572" class="Symbol">)</a>
<a id="574" class="Keyword">open</a> <a id="579" class="Keyword">import</a> <a id="586" href="Data.Product.html" class="Module">Data.Product</a>    <a id="602" class="Keyword">using</a> <a id="608" class="Symbol">(</a> <a id="610" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="614" class="Symbol">;</a> <a id="616" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="620" class="Symbol">)</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="Relation.Unary.html" class="Module">Relation.Unary</a>  <a id="650" class="Keyword">using</a> <a id="656" class="Symbol">(</a> <a id="658" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="663" class="Symbol">;</a> <a id="665" href="Relation.Unary.html#1523" class="Function Operator">_∈_</a> <a id="669" class="Symbol">)</a>

<a id="672" class="Comment">-- Imports from agda-algebras --------------------------------------------------------------</a>
<a id="765" class="Keyword">open</a> <a id="770" class="Keyword">import</a> <a id="777" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>         <a id="808" class="Keyword">using</a> <a id="814" class="Symbol">(</a> <a id="816" href="Overture.Preliminaries.html#3617" class="Datatype">𝟘</a> <a id="818" class="Symbol">;</a> <a id="820" href="Overture.Preliminaries.html#3693" class="Datatype">𝟙</a> <a id="822" class="Symbol">;</a> <a id="824" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="826" class="Symbol">;</a> <a id="828" href="Overture.Preliminaries.html#3845" class="Datatype">𝟛</a> <a id="830" class="Symbol">)</a>
<a id="832" class="Keyword">open</a> <a id="837" class="Keyword">import</a> <a id="844" href="Relations.Continuous.html" class="Module">Relations.Continuous</a>           <a id="875" class="Keyword">using</a> <a id="881" class="Symbol">(</a> <a id="883" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="887" class="Symbol">)</a>
<a id="889" class="Keyword">open</a> <a id="894" class="Keyword">import</a> <a id="901" href="Structures.Basic.html" class="Module">Structures.Basic</a>               <a id="932" class="Keyword">using</a> <a id="938" class="Symbol">(</a> <a id="940" href="Structures.Basic.html#1234" class="Record">signature</a> <a id="950" class="Symbol">;</a> <a id="952" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="962" class="Symbol">)</a>
<a id="964" class="Keyword">open</a> <a id="969" class="Keyword">import</a> <a id="976" href="Examples.Structures.Signatures.html" class="Module">Examples.Structures.Signatures</a> <a id="1007" class="Keyword">using</a> <a id="1013" class="Symbol">(</a> <a id="1015" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="1018" class="Symbol">;</a> <a id="1020" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="1025" class="Symbol">;</a> <a id="1027" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a><a id="1031" class="Symbol">)</a>
<a id="1033" class="Keyword">open</a> <a id="1038" class="Keyword">import</a> <a id="1045" href="Structures.Homs.html" class="Module">Structures.Homs</a>                <a id="1076" class="Keyword">using</a> <a id="1082" class="Symbol">(</a> <a id="1084" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="1088" class="Symbol">)</a>
<a id="1090" class="Keyword">open</a> <a id="1095" href="Structures.Basic.html#1234" class="Module">signature</a>
<a id="1105" class="Keyword">open</a> <a id="1110" href="Structures.Basic.html#1568" class="Module">structure</a>

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
<a id="3160" class="Keyword">module</a> <a id="solution-2-1"></a><a id="3167" href="Exercises.Complexity.FiniteCSP.html#3167" class="Module">solution-2-1</a> <a id="3180" class="Keyword">where</a>

 <a id="3188" class="Comment">-- The (purely) relational structure with</a>
 <a id="3231" class="Comment">-- + 2-element domain,</a>
 <a id="3255" class="Comment">-- + one binary relation Rᵃ := \{(0,0), (1, 1)\}</a>

 <a id="3306" class="Keyword">data</a> <a id="solution-2-1.Rᵃ"></a><a id="3311" href="Exercises.Complexity.FiniteCSP.html#3311" class="Datatype">Rᵃ</a> <a id="3314" class="Symbol">:</a> <a id="3316" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="3321" class="Symbol">(</a><a id="3322" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="3324" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="3326" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a><a id="3327" class="Symbol">)</a> <a id="3329" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a> <a id="3332" class="Keyword">where</a>
  <a id="solution-2-1.Rᵃ.r1"></a><a id="3340" href="Exercises.Complexity.FiniteCSP.html#3340" class="InductiveConstructor">r1</a> <a id="3343" class="Symbol">:</a> <a id="3345" class="Symbol">(</a><a id="3346" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="3350" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3352" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="3356" class="Symbol">)</a> <a id="3358" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3360" href="Exercises.Complexity.FiniteCSP.html#3311" class="Datatype">Rᵃ</a>
  <a id="solution-2-1.Rᵃ.r2"></a><a id="3365" href="Exercises.Complexity.FiniteCSP.html#3365" class="InductiveConstructor">r2</a> <a id="3368" class="Symbol">:</a> <a id="3370" class="Symbol">(</a><a id="3371" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="3375" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3377" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="3381" class="Symbol">)</a> <a id="3383" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3385" href="Exercises.Complexity.FiniteCSP.html#3311" class="Datatype">Rᵃ</a>

 <a id="solution-2-1.𝑨"></a><a id="3390" href="Exercises.Complexity.FiniteCSP.html#3390" class="Function">𝑨</a> <a id="3392" class="Symbol">:</a> <a id="3394" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3404" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="3410" class="Comment">-- (no operation symbols)</a>
               <a id="3451" href="Examples.Structures.Signatures.html#893" class="Function">S001</a>  <a id="3457" class="Comment">-- (one binary relation symbol)</a>

 <a id="3491" href="Exercises.Complexity.FiniteCSP.html#3390" class="Function">𝑨</a> <a id="3493" class="Symbol">=</a> <a id="3495" class="Keyword">record</a> <a id="3502" class="Symbol">{</a> <a id="3504" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="3512" class="Symbol">=</a> <a id="3514" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a>
            <a id="3528" class="Symbol">;</a> <a id="3530" href="Structures.Basic.html#1739" class="Field">op</a> <a id="3533" class="Symbol">=</a> <a id="3535" class="Symbol">λ</a> <a id="3537" class="Symbol">()</a>
            <a id="3552" class="Symbol">;</a> <a id="3554" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="3558" class="Symbol">=</a> <a id="3560" class="Symbol">λ</a> <a id="3562" href="Exercises.Complexity.FiniteCSP.html#3562" class="Bound">_</a> <a id="3564" href="Exercises.Complexity.FiniteCSP.html#3564" class="Bound">x</a> <a id="3566" class="Symbol">→</a> <a id="3568" class="Symbol">((</a><a id="3570" href="Exercises.Complexity.FiniteCSP.html#3564" class="Bound">x</a> <a id="3572" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="3575" class="Symbol">)</a> <a id="3577" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3579" class="Symbol">(</a><a id="3580" href="Exercises.Complexity.FiniteCSP.html#3564" class="Bound">x</a> <a id="3582" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a><a id="3585" class="Symbol">))</a> <a id="3588" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="3590" href="Exercises.Complexity.FiniteCSP.html#3311" class="Datatype">Rᵃ</a>
            <a id="3605" class="Symbol">}</a>


 <a id="3610" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures Sig∅ Sig001, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="solution-2-1.claim"></a><a id="3718" href="Exercises.Complexity.FiniteCSP.html#3718" class="Function">claim</a> <a id="3724" class="Symbol">:</a> <a id="3726" class="Symbol">(</a><a id="3727" href="Exercises.Complexity.FiniteCSP.html#3727" class="Bound">𝑩</a> <a id="3729" class="Symbol">:</a> <a id="3731" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="3741" class="Symbol">{</a><a id="3742" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3744" class="Symbol">}{</a><a id="3746" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3748" class="Symbol">}{</a><a id="3750" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3752" class="Symbol">}{</a><a id="3754" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3756" class="Symbol">}</a> <a id="3758" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a> <a id="3761" href="Examples.Structures.Signatures.html#893" class="Function">S001</a> <a id="3766" class="Symbol">{</a><a id="3767" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3769" class="Symbol">}{</a><a id="3771" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a><a id="3773" class="Symbol">})</a> <a id="3776" class="Symbol">→</a> <a id="3778" href="Structures.Homs.html#2787" class="Function">hom</a> <a id="3782" href="Exercises.Complexity.FiniteCSP.html#3727" class="Bound">𝑩</a> <a id="3784" href="Exercises.Complexity.FiniteCSP.html#3390" class="Function">𝑨</a>
 <a id="3787" href="Exercises.Complexity.FiniteCSP.html#3718" class="Function">claim</a> <a id="3793" href="Exercises.Complexity.FiniteCSP.html#3793" class="Bound">𝑩</a> <a id="3795" class="Symbol">=</a> <a id="3797" class="Symbol">(λ</a> <a id="3800" href="Exercises.Complexity.FiniteCSP.html#3800" class="Bound">x</a> <a id="3802" class="Symbol">→</a> <a id="3804" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="3807" class="Symbol">)</a> <a id="3809" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3811" class="Symbol">(λ</a> <a id="3814" href="Exercises.Complexity.FiniteCSP.html#3814" class="Bound">_</a> <a id="3816" href="Exercises.Complexity.FiniteCSP.html#3816" class="Bound">_</a> <a id="3818" href="Exercises.Complexity.FiniteCSP.html#3818" class="Bound">_</a> <a id="3820" class="Symbol">→</a> <a id="3822" href="Exercises.Complexity.FiniteCSP.html#3340" class="InductiveConstructor">r1</a><a id="3824" class="Symbol">)</a> <a id="3826" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3828" class="Symbol">λ</a> <a id="3830" class="Symbol">()</a>

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

<a id="4971" class="Keyword">module</a> <a id="solution-2-2"></a><a id="4978" href="Exercises.Complexity.FiniteCSP.html#4978" class="Module">solution-2-2</a> <a id="4991" class="Keyword">where</a>

 <a id="4999" class="Comment">-- The (purely) relational structure with</a>
 <a id="5042" class="Comment">-- + 2-element domain,</a>
 <a id="5066" class="Comment">-- + one binary relation: Rᵃ := { (0,0), (1, 1) }</a>
 <a id="5117" class="Comment">-- + two unary relations: C₀ᵃ := { 0 } , C₁ᵃ := { 1 }</a>

 <a id="5173" class="Keyword">data</a> <a id="solution-2-2.Rᵃ"></a><a id="5178" href="Exercises.Complexity.FiniteCSP.html#5178" class="Datatype">Rᵃ</a> <a id="5181" class="Symbol">:</a> <a id="5183" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5188" class="Symbol">(</a><a id="5189" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5191" href="Data.Product.html#1167" class="Function Operator">×</a> <a id="5193" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a><a id="5194" class="Symbol">)</a> <a id="5196" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a> <a id="5199" class="Keyword">where</a>
  <a id="solution-2-2.Rᵃ.r1"></a><a id="5207" href="Exercises.Complexity.FiniteCSP.html#5207" class="InductiveConstructor">r1</a> <a id="5210" class="Symbol">:</a> <a id="5212" class="Symbol">(</a><a id="5213" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5217" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5219" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5223" class="Symbol">)</a> <a id="5225" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5227" href="Exercises.Complexity.FiniteCSP.html#5178" class="Datatype">Rᵃ</a>
  <a id="solution-2-2.Rᵃ.r2"></a><a id="5232" href="Exercises.Complexity.FiniteCSP.html#5232" class="InductiveConstructor">r2</a> <a id="5235" class="Symbol">:</a> <a id="5237" class="Symbol">(</a><a id="5238" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5242" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5244" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5248" class="Symbol">)</a> <a id="5250" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5252" href="Exercises.Complexity.FiniteCSP.html#5178" class="Datatype">Rᵃ</a>

 <a id="5257" class="Keyword">data</a> <a id="solution-2-2.C₀ᵃ"></a><a id="5262" href="Exercises.Complexity.FiniteCSP.html#5262" class="Datatype">C₀ᵃ</a> <a id="5266" class="Symbol">:</a> <a id="5268" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5273" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5275" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a> <a id="5278" class="Keyword">where</a>
  <a id="solution-2-2.C₀ᵃ.c₀"></a><a id="5286" href="Exercises.Complexity.FiniteCSP.html#5286" class="InductiveConstructor">c₀</a> <a id="5289" class="Symbol">:</a> <a id="5291" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a> <a id="5295" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5297" href="Exercises.Complexity.FiniteCSP.html#5262" class="Datatype">C₀ᵃ</a>

 <a id="5303" class="Keyword">data</a> <a id="solution-2-2.C₁ᵃ"></a><a id="5308" href="Exercises.Complexity.FiniteCSP.html#5308" class="Datatype">C₁ᵃ</a> <a id="5312" class="Symbol">:</a> <a id="5314" href="Relation.Unary.html#1101" class="Function">Pred</a> <a id="5319" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5321" href="Exercises.Complexity.FiniteCSP.html#569" class="Primitive">ℓ₀</a> <a id="5324" class="Keyword">where</a>
  <a id="solution-2-2.C₁ᵃ.c₁"></a><a id="5332" href="Exercises.Complexity.FiniteCSP.html#5332" class="InductiveConstructor">c₁</a> <a id="5335" class="Symbol">:</a> <a id="5337" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a> <a id="5341" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5343" href="Exercises.Complexity.FiniteCSP.html#5308" class="Datatype">C₁ᵃ</a>


 <a id="solution-2-2.𝑨"></a><a id="5350" href="Exercises.Complexity.FiniteCSP.html#5350" class="Function">𝑨</a> <a id="5352" class="Symbol">:</a> <a id="5354" href="Structures.Basic.html#1568" class="Record">structure</a> <a id="5364" href="Examples.Structures.Signatures.html#565" class="Function">S∅</a>    <a id="5370" class="Comment">-- (no operations)</a>
               <a id="5404" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a>  <a id="5410" class="Comment">-- (two unary relations and one binary relation)</a>

 <a id="5461" href="Exercises.Complexity.FiniteCSP.html#5350" class="Function">𝑨</a> <a id="5463" class="Symbol">=</a> <a id="5465" class="Keyword">record</a> <a id="5472" class="Symbol">{</a> <a id="5474" href="Structures.Basic.html#1720" class="Field">carrier</a> <a id="5482" class="Symbol">=</a> <a id="5484" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a>
            <a id="5498" class="Symbol">;</a> <a id="5500" href="Structures.Basic.html#1739" class="Field">op</a> <a id="5503" class="Symbol">=</a> <a id="5505" class="Symbol">λ</a> <a id="5507" class="Symbol">()</a>
            <a id="5522" class="Symbol">;</a> <a id="5524" href="Structures.Basic.html#1823" class="Field">rel</a> <a id="5528" class="Symbol">=</a> <a id="5530" href="Exercises.Complexity.FiniteCSP.html#5579" class="Function">rels</a>
            <a id="5547" class="Symbol">}</a>
            <a id="5561" class="Keyword">where</a>
            <a id="5579" href="Exercises.Complexity.FiniteCSP.html#5579" class="Function">rels</a> <a id="5584" class="Symbol">:</a> <a id="5586" class="Symbol">(</a><a id="5587" href="Exercises.Complexity.FiniteCSP.html#5587" class="Bound">r</a> <a id="5589" class="Symbol">:</a> <a id="5591" href="Overture.Preliminaries.html#3845" class="Datatype">𝟛</a><a id="5592" class="Symbol">)</a> <a id="5594" class="Symbol">→</a> <a id="5596" href="Relations.Continuous.html#3907" class="Function">Rel</a> <a id="5600" href="Overture.Preliminaries.html#3748" class="Datatype">𝟚</a> <a id="5602" class="Symbol">(</a><a id="5603" href="Structures.Basic.html#1313" class="Field">arity</a> <a id="5609" href="Examples.Structures.Signatures.html#1148" class="Function">S021</a> <a id="5614" href="Exercises.Complexity.FiniteCSP.html#5587" class="Bound">r</a><a id="5615" class="Symbol">)</a>
            <a id="5629" href="Exercises.Complexity.FiniteCSP.html#5579" class="Function">rels</a> <a id="5634" href="Overture.Preliminaries.html#3864" class="InductiveConstructor">𝟛.𝟎</a> <a id="5638" href="Exercises.Complexity.FiniteCSP.html#5638" class="Bound">x</a> <a id="5640" class="Symbol">=</a> <a id="5642" class="Symbol">((</a><a id="5644" href="Exercises.Complexity.FiniteCSP.html#5638" class="Bound">x</a> <a id="5646" href="Overture.Preliminaries.html#3798" class="InductiveConstructor">𝟚.𝟎</a><a id="5649" class="Symbol">)</a> <a id="5651" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="5653" class="Symbol">(</a><a id="5654" href="Exercises.Complexity.FiniteCSP.html#5638" class="Bound">x</a> <a id="5656" href="Overture.Preliminaries.html#3807" class="InductiveConstructor">𝟚.𝟏</a><a id="5659" class="Symbol">))</a> <a id="5662" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5664" href="Exercises.Complexity.FiniteCSP.html#5178" class="Datatype">Rᵃ</a>
            <a id="5679" href="Exercises.Complexity.FiniteCSP.html#5579" class="Function">rels</a> <a id="5684" href="Overture.Preliminaries.html#3873" class="InductiveConstructor">𝟛.𝟏</a> <a id="5688" href="Exercises.Complexity.FiniteCSP.html#5688" class="Bound">x</a> <a id="5690" class="Symbol">=</a> <a id="5692" href="Exercises.Complexity.FiniteCSP.html#5688" class="Bound">x</a> <a id="5694" href="Overture.Preliminaries.html#3712" class="InductiveConstructor">𝟙.𝟎</a> <a id="5698" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5700" href="Exercises.Complexity.FiniteCSP.html#5262" class="Datatype">C₀ᵃ</a>
            <a id="5716" href="Exercises.Complexity.FiniteCSP.html#5579" class="Function">rels</a> <a id="5721" href="Overture.Preliminaries.html#3882" class="InductiveConstructor">𝟛.𝟐</a> <a id="5725" href="Exercises.Complexity.FiniteCSP.html#5725" class="Bound">x</a> <a id="5727" class="Symbol">=</a> <a id="5729" href="Exercises.Complexity.FiniteCSP.html#5725" class="Bound">x</a> <a id="5731" href="Overture.Preliminaries.html#3712" class="InductiveConstructor">𝟙.𝟎</a> <a id="5735" href="Relation.Unary.html#1523" class="Function Operator">∈</a> <a id="5737" href="Exercises.Complexity.FiniteCSP.html#5308" class="Datatype">C₁ᵃ</a>


 <a id="5744" class="Comment">-- Claim: Given an arbitrary 𝑩 in the signatures S∅ S021, we can construct a homomorphism from 𝑩 to 𝑨.</a>
 <a id="5848" class="Comment">-- claim :  (𝑩 : structure S∅ S021 {ℓ₀}{ℓ₀})</a>
 <a id="5894" class="Comment">--  →       (∀ (x : 𝟚 → carrier 𝑩)</a>
 <a id="5930" class="Comment">--           → (rel 𝑩) 𝟛.𝟎 x  -- if ((x 𝟚.𝟎) , (x 𝟚.𝟏)) ∈ Rᵇ, then...</a>
 <a id="6001" class="Comment">--           → ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟎)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟏)))</a>
 <a id="6079" class="Comment">--             × ((rel 𝑩) 𝟛.𝟏 (λ _ → (x 𝟚.𝟏)) → ¬ (rel 𝑩) 𝟛.𝟐 (λ _ → (x 𝟚.𝟎)))</a>
 <a id="6159" class="Comment">--          --  × (x 𝟚.𝟎 ∈ C₁ᵇ → x 𝟚.𝟏 ∉ C₀ᵇ))</a>
 <a id="6207" class="Comment">--          )</a>
 <a id="6222" class="Comment">--  →       hom 𝑩 𝑨</a>
 <a id="6243" class="Comment">-- claim 𝑩 x = {!!}</a>

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


