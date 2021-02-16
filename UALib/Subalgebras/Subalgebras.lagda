---
layout: default
title : UALib.Subalgebras.Subalgebras module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="subalgebra-types">Subalgebras</a>

The [UALib.Subalgebras.Subalgebras][] module of the [Agda Universal Algebra Library][] defins the `Subalgebra` type, representing the subalgebra of a given algebra, as well as the collection of all subalgebras of a given class of algebras.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)

module UALib.Subalgebras.Subalgebras
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import UALib.Subalgebras.Homomorphisms {𝑆 = 𝑆}{gfe}{𝕏} public
open import UALib.Prelude.Preliminaries using (∘-embedding; id-is-embedding)

\end{code}



#### <a id="subalgebra-type">Subalgebra type</a>

Given algebras 𝑨 : Algebra 𝓦 𝑆 and 𝑩 : Algebra 𝓤 𝑆, we say that 𝑩 is a **subalgebra** of 𝑨, and we write 𝑩 IsSubalgebraOf 𝑨 just in case 𝑩 can be embedded in 𝑨; in other terms, there exists a map h : ∣ 𝑨 ∣ → ∣ 𝑩 ∣ from the universe of 𝑨 to the universe of 𝑩 such that h is an embedding (i.e., is-embedding h holds) and h is a homomorphism from 𝑨 to 𝑩.

\begin{code}

_IsSubalgebraOf_ : {𝓤 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ hom 𝑩 𝑨 , is-embedding ∣ h ∣

Subalgebra : {𝓤 𝓦 : Universe} → Algebra 𝓦 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇
Subalgebra {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOf 𝑨

\end{code}


#### <a id="consequences-of-first-homomorphism-theorem">Consequences of First Homomorphism Theorem</a>

We take this opportunity to prove a useful lemma that requires the `IsSubalgebraOf` function.  If 𝑨 is an 𝑆-algebra, and if `h : hom (𝑻 X) 𝑨` is a homomorphism from the term algebra to 𝑨, then the quotient 𝑻(X) ╱ (ker h) is (isomorphic to) a subalgebra of 𝑨.

\begin{code}

open Congruence

FirstHomCorollary : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
                    --extensionality assumptions:
 →                     propext 𝓦 → is-set ∣ 𝑩 ∣
 →                     (∀ a x → is-subsingleton (⟨ kercon 𝑨{𝑩} h ⟩ a x))
 →                     (∀ C → is-subsingleton (𝒞{A = ∣ 𝑨 ∣}{⟨ kercon 𝑨{𝑩} h ⟩} C))
                    -------------------------------------------------------------
 →                  (𝑨 [ 𝑩 ]/ker h) IsSubalgebraOf 𝑩

FirstHomCorollary 𝑨 𝑩 h pe Bset ssR ssA = ϕhom , ϕemb
 where
  FirstHomThm : Σ ϕ ꞉ hom (𝑨 [ 𝑩 ]/ker h) 𝑩 , (∣ h ∣ ≡ ∣ ϕ ∣ ∘ ∣ πker 𝑨 {𝑩} h ∣ ) × Monic ∣ ϕ ∣ × is-embedding ∣ ϕ ∣
  FirstHomThm = FirstHomomorphismTheorem 𝑨 𝑩 h pe Bset ssR ssA
  ϕhom : hom (𝑨 [ 𝑩 ]/ker h) 𝑩
  ϕhom = ∣ FirstHomThm ∣
  ϕemb : is-embedding ∣ ϕhom ∣
  ϕemb = snd (snd (snd FirstHomThm))


free-quot-subalg : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑨 : Algebra 𝓤 𝑆}{h : hom (𝑻 X) 𝑨}
                    --extensionality assumptions:
 →                    propext 𝓤 → is-set ∣ 𝑨 ∣
 →                    (∀ p q → is-subsingleton (⟨ kercon (𝑻 X){𝑨} h ⟩ p q))
 →                    (∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon (𝑻 X){𝑨} h ⟩} C))
                   -------------------------------------------------------------------
 →                 ((𝑻 X) [ 𝑨 ]/ker h) IsSubalgebraOf 𝑨

free-quot-subalg {𝓤}{𝓧}{X}{𝑨}{h} pe Aset ssR ssA = FirstHomCorollary (𝑻 X) 𝑨 h pe Aset ssR ssA

\end{code}




##### <a id="syntactic-sugar">Syntactic sugar</a>

We use the convenient ≤ notation for the subalgebra relation.

\begin{code}
_≤_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨
\end{code}


#### <a id="subalgebras-of-a-class">Subalgebras of a class</a>

\begin{code}

_IsSubalgebraOfClass_ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆) → Pred (Algebra 𝓠 𝑆) 𝓦 → _ ̇
_IsSubalgebraOfClass_ {𝓤} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ SA ꞉ (Subalgebra{𝓤} 𝑨) ,
                                                              (𝑨 ∈ 𝒦)  × (𝑩 ≅ ∣ SA ∣)

SUBALGEBRAOFCLASS : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → _ ̇
SUBALGEBRAOFCLASS {𝓤} 𝒦 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOfClass 𝒦

SubalgebraOfClass : {𝓤 𝓠 : Universe} → Pred (Algebra 𝓠 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺) → 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SubalgebraOfClass {𝓤}{𝓠} = SUBALGEBRAOFCLASS {𝓤}{𝓠}{𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺}

\end{code}

#### <a id="subalgebra-lemmas">Subalgebra lemmas</a>

Here are a number of useful facts about subalgebras.  Many of them seem redundant, and they are to some extent.  However, each one differs slightly from the next, if only with respect to the explicitness or implicitness of their arguments.  The aim is to make it as convenient as possible to apply the lemmas in different situations.  (We're in the UALib utility closet now, and elegance is not the priority.)

\begin{code}

--Transitivity of IsSubalgebra (explicit args)
TRANS-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
 →        𝑩 ≤ 𝑨   →    𝑪 ≤ 𝑩
          ------------------
 →        𝑪 ≤ 𝑨

TRANS-≤ 𝑨 𝑩 𝑪 BA CB = (HomComp 𝑪 𝑨 ∣ CB ∣ ∣ BA ∣) , ∘-embedding ∥ BA ∥ ∥ CB ∥

--Transitivity of IsSubalgebra (implicit args)
Trans-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →        𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑩 → 𝑪 ≤ 𝑨

Trans-≤ 𝑨 {𝑩} 𝑪 = TRANS-≤ 𝑨 𝑩 𝑪


--Transitivity of IsSubalgebra (implicit args)
trans-≤ : {𝓧 𝓨 𝓩 : Universe}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
 →        𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑩 → 𝑪 ≤ 𝑨

trans-≤ {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪} = TRANS-≤ 𝑨 𝑩 𝑪


transitivity-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
 →               𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪

transitivity-≤ 𝑨 {𝑩}{𝑪} A≤B B≤C = ϕ , ϕemb
 where
  ϕ : hom 𝑨 𝑪
  ϕ = ((fst ∣ B≤C ∣) ∘ (fst ∣ A≤B ∣) , (∘-hom 𝑨 𝑩 𝑪 {fst ∣ A≤B ∣}{fst ∣ B≤C ∣}(snd ∣ A≤B ∣)(snd ∣ B≤C ∣)))
  ϕemb : is-embedding ∣ ϕ ∣
  ϕemb = ∘-embedding (∥ B≤C ∥)(∥ A≤B ∥)


--Reflexivity of IsSubalgebra (explicit arg)
REFL-≤ : {𝓤 : Universe}(𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≤ 𝑨
REFL-≤ 𝑨 = (𝑖𝑑 ∣ 𝑨 ∣ , id-is-hom) , id-is-embedding


--Reflexivity of IsSubalgebra (implicit arg)
refl-≤ : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≤ 𝑨
refl-≤ {𝑨 = 𝑨} = REFL-≤ 𝑨


--Reflexivity of IsSubalgebra (explicit arg)
ISO-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
 →      𝑩 ≤ 𝑨   →   𝑪 ≅ 𝑩
        -----------------
 →      𝑪 ≤ 𝑨

ISO-≤ 𝑨 𝑩 𝑪 B≤A C≅B = (g ∘ f , gfhom) , gfemb
 where
  f : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  f = fst ∣ C≅B ∣
  g : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  g = fst ∣ B≤A ∣

  gfemb : is-embedding (g ∘ f)
  gfemb = ∘-embedding (∥ B≤A ∥) (iso→embedding C≅B)

  gfhom : is-homomorphism 𝑪 𝑨 (g ∘ f)
  gfhom = ∘-hom 𝑪 𝑩 𝑨 {f}{g} (snd ∣ C≅B ∣) (snd ∣ B≤A ∣)


Iso-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →      𝑩 ≤ 𝑨 → 𝑪 ≅ 𝑩 → 𝑪 ≤ 𝑨

Iso-≤ 𝑨 {𝑩} 𝑪 = ISO-≤ 𝑨 𝑩 𝑪


iso-≤ : {𝓧 𝓨 𝓩 : Universe}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →      𝑩 ≤ 𝑨 → 𝑪 ≅ 𝑩 → 𝑪 ≤ 𝑨

iso-≤ {𝑨 = 𝑨} {𝑩 = 𝑩} 𝑪 = ISO-≤ 𝑨 𝑩 𝑪


trans-≤-≅ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →          𝑨 ≤ 𝑩 → 𝑨 ≅ 𝑪 → 𝑪 ≤ 𝑩

trans-≤-≅ {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} 𝑪 A≤B B≅C = ISO-≤ 𝑩 𝑨 𝑪 A≤B (sym-≅ B≅C)


TRANS-≤-≅ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →          𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪

TRANS-≤-≅ {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} 𝑪 A≤B B≅C = (HomComp 𝑨 𝑪 ∣ A≤B ∣ ∣ B≅C ∣) , ∘-embedding (iso→embedding B≅C)(∥ A≤B ∥)


lift-alg-lower-≤-lift : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →                      𝑨 ≤ 𝑩 → 𝑨 ≤ (lift-alg 𝑩 𝓩)
lift-alg-lower-≤-lift {𝓧}{𝓨}{𝓩}𝑨 {𝑩} A≤B = TRANS-≤-≅ 𝑨 {𝑩} (lift-alg 𝑩 𝓩) A≤B lift-alg-≅


mono-≤ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆){𝒦 𝒦' : Pred (Algebra 𝓠 𝑆) 𝓦}
 →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'

mono-≤ 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥


lift-alg-is-sub : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}{𝑩 : Algebra 𝓤 𝑆}
 →                𝑩 IsSubalgebraOfClass 𝒦 → (lift-alg 𝑩 𝓤) IsSubalgebraOfClass 𝒦

lift-alg-is-sub {𝓤}{𝒦}{𝑩}(𝑨 , (sa , (KA , B≅sa))) =
 𝑨 , sa , KA , trans-≅ _ _ _ (sym-≅ lift-alg-≅) B≅sa


lift-alg-lift-≤-lower : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →                      𝑩 ≤ 𝑨 → (lift-alg 𝑩 𝓩) ≤ 𝑨

lift-alg-lift-≤-lower {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} B≤A =
 iso-≤{𝓧}{𝓨}{𝓩 = (𝓨 ⊔ 𝓩)}{𝑨}{𝑩} (lift-alg 𝑩 𝓩) B≤A (sym-≅ lift-alg-≅)


lift-alg-lower-≤-lift' : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →                      𝑩 ≤ 𝑨 → 𝑩 ≤ (lift-alg 𝑨 𝓩)

lift-alg-lower-≤-lift' {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} B≤A = TRANS-≤-≅ 𝑩 {𝑨} (lift-alg 𝑨 𝓩) B≤A lift-alg-≅


lift-alg-sub-lift : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                  𝑪 ≤ 𝑨 → 𝑪 ≤ (lift-alg 𝑨 𝓦)

lift-alg-sub-lift {𝓤}{𝓦} 𝑨 {𝑪} C≤A = TRANS-≤-≅ 𝑪 {𝑨} (lift-alg 𝑨 𝓦) C≤A lift-alg-≅


lift-alg-≤ : {𝓧 𝓨 𝓩 𝓦 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →           𝑨 ≤ 𝑩 → (lift-alg 𝑨 𝓩) ≤ (lift-alg 𝑩 𝓦)

lift-alg-≤ {𝓧}{𝓨}{𝓩}{𝓦} 𝑨 {𝑩} A≤B =
 transitivity-≤ lA {𝑩}{lift-alg 𝑩 𝓦} (transitivity-≤ lA {𝑨}{𝑩} lAA A≤B) B≤lB
  where
   lA : Algebra (𝓧 ⊔ 𝓩) 𝑆
   lA = lift-alg 𝑨 𝓩

   lAA : lA ≤ 𝑨
   lAA = lift-alg-lift-≤-lower 𝑨 {𝑨} refl-≤

   B≤lB : 𝑩 ≤ lift-alg 𝑩 𝓦
   B≤lB = lift-alg-lower-≤-lift 𝑩 {𝑩} refl-≤

\end{code}

---------------------------------

[← UALib.Subalgebras.Homomorphisms](UALib.Subalgebras.Homomorphisms.html)
<span style="float:right;">[UALib.Subalgebras.WWMD →](UALib.Subalgebras.WWMD.html)</span>

{% include UALib.Links.md %}

