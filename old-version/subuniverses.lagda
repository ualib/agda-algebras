---
layout: default
title : subuniverses module (of the Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: subuniverses.agda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 12 Jan 2021
-->

## Subalgebras

### Options, imports
\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext)

module subuniverses
 {𝑆 : Signature 𝓞 𝓥} {gfe : global-dfunext}
 {𝕏 : {𝓧 𝓤 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import Relation.Unary using (⋂)

open import congruences {𝑆 = 𝑆}{gfe}
open import homomorphisms {𝑆 = 𝑆}{gfe}
open import terms {𝑆 = 𝑆} {gfe} {𝕏} renaming (generator to ℊ)
open import prelude using (_●_; lr-implication; rl-implication; Im_⊆_;
 id-is-embedding; pr₁-embedding; embedding-gives-ap-is-equiv; ∘-embedding;
 ×-is-subsingleton; inverse; logically-equivalent-subsingletons-are-equivalent) public
\end{code}

### Subuniverses

\begin{code}
Subuniverses : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆) → Pred (Pred ∣ 𝑨 ∣ 𝓤) (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤)
Subuniverses 𝑨 B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → Im a ⊆ B → (f ̂ 𝑨) a ∈ B

SubunivAlg : {𝓠 𝓤 : Universe} (𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →           B ∈ Subuniverses 𝑨
 →           Algebra (𝓠 ⊔ 𝓤) 𝑆
SubunivAlg 𝑨 B B∈SubA = Σ B , λ f x → (f ̂ 𝑨)(∣_∣ ∘ x) ,
                                            B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

record Subuniverse {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆} : 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ 𝑨 ∣ 𝓤
   isSub : sset ∈ Subuniverses 𝑨
\end{code}

### Subuniverse generation

\begin{code}
data Sg {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆) (X : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
 var : ∀ {v} → v ∈ X → v ∈ Sg 𝑨 X
 app : (f : ∣ 𝑆 ∣){a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣} → Im a ⊆ Sg 𝑨 X
       ---------------------------------------------
  →       (f ̂ 𝑨) a ∈ Sg 𝑨 X

sgIsSub : {𝓠 𝓤 : Universe}{𝑨 : Algebra 𝓠 𝑆}{X : Pred ∣ 𝑨 ∣ 𝓤} → Sg 𝑨 X ∈ Subuniverses 𝑨
sgIsSub f a α = app f α

sgIsSmallest : {𝓠 𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓠 𝑆){X : Pred ∣ 𝑨 ∣ 𝓤}(Y : Pred ∣ 𝑨 ∣ 𝓦)
 →             Y ∈ Subuniverses 𝑨  →  X ⊆ Y
              ------------------------------
 →                     Sg 𝑨 X ⊆ Y

-- By induction on x ∈ Sg X, show x ∈ Y
sgIsSmallest _ _ _ X⊆Y (var v∈X) = X⊆Y v∈X

sgIsSmallest 𝑨 Y YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
 where
  -- First, show the args are in Y
  ima⊆Y : Im a ⊆ Y
  ima⊆Y i = sgIsSmallest 𝑨 Y YIsSub X⊆Y (ima⊆SgX i)

  --Since Y is a subuniverse of 𝑨, it contains the application
  app∈Y : (f ̂ 𝑨) a ∈ Y          --           of f to said args.
  app∈Y = YIsSub f a ima⊆Y
\end{code}

### Subuniverse properties

#### Intersections of subuniverses are subuniverses

\begin{code}
sub-inter-is-sub : {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)
                   (I : 𝓤 ̇)(𝒜 : I → Pred ∣ 𝑨 ∣ 𝓤)
 →                 ((i : I) → 𝒜 i ∈ Subuniverses 𝑨)
                  -------------------------------------
 →                  ⋂ I 𝒜 ∈ Subuniverses 𝑨

sub-inter-is-sub 𝑨 I 𝒜 Ai-is-Sub f a ima⊆⋂A = α
 where
  α : (f ̂ 𝑨) a ∈ ⋂ I 𝒜
  α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i
\end{code}

#### Compatibility with term operations

\begin{code}
sub-term-closed : {𝓧 𝓠 𝓤 : Universe}{X : 𝓧 ̇}(𝑨 : Algebra 𝓠 𝑆)(B : Pred ∣ 𝑨 ∣ 𝓤)
 →                B ∈ Subuniverses 𝑨
 →                (t : Term)(b : X → ∣ 𝑨 ∣)
 →                (∀ x → b x ∈ B)
                ---------------------------
 →                ((t ̇ 𝑨) b) ∈ B

sub-term-closed _ _ B≤A (ℊ x) b b∈B = b∈B x

sub-term-closed 𝑨 B B≤A (node f t) b b∈B =
   B≤A f (λ z → (t z ̇ 𝑨) b)
          (λ x → sub-term-closed 𝑨 B B≤A (t x) b b∈B)
\end{code}

### Term images

\begin{code}
data TermImage {𝓠 𝓤 : Universe}(𝑨 : Algebra 𝓠 𝑆)(Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤) where
 var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage 𝑨 Y
 app : (f : ∣ 𝑆 ∣) (t : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣) → (∀ i  →  t i ∈ TermImage 𝑨 Y)
      ---------------------------------------------------------------
  →              (f ̂ 𝑨) t ∈ TermImage 𝑨 Y

--1. TermImage is a subuniverse
TermImageIsSub : {𝓠 𝓤 : Universe}
                 {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
                 ------------------------------------
 →                TermImage 𝑨 Y ∈ Subuniverses 𝑨

TermImageIsSub = app -- λ f a x → app f a x

--2. Y ⊆ TermImageY
Y⊆TermImageY : {𝓠 𝓤 : Universe}
               {𝑨 : Algebra 𝓠 𝑆}{Y : Pred ∣ 𝑨 ∣ 𝓤}
              ------------------------------------
 →              Y ⊆ TermImage 𝑨 Y

Y⊆TermImageY {a} a∈Y = var a∈Y

-- 3. Sg^A(Y) is the smallest subuniverse containing Y
--    Proof: see `sgIsSmallest`

SgY⊆TermImageY : {𝓠 𝓤 : Universe}
                 (𝑨 : Algebra 𝓠 𝑆)  (Y : Pred ∣ 𝑨 ∣ 𝓤)
                --------------------------------------
 →                Sg 𝑨 Y ⊆ TermImage 𝑨 Y

SgY⊆TermImageY 𝑨 Y = sgIsSmallest 𝑨 (TermImage 𝑨 Y) TermImageIsSub Y⊆TermImageY
\end{code}

### Homomorphic images

\begin{code}
hom-image-is-sub : {𝓠 𝓤 : Universe} → global-dfunext
 →                 {𝑨 : Algebra 𝓠 𝑆} {𝑩 : Algebra 𝓤 𝑆} (ϕ : hom 𝑨 𝑩)
                  -------------------------------------------------
 →                 (HomImage 𝑩 ϕ) ∈ Subuniverses 𝑩

hom-image-is-sub gfe {𝑨}{𝑩} ϕ f b b∈Imf = eq ((f ̂ 𝑩) b) ((f ̂ 𝑨) ar) γ
 where
  ar : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣
  ar = λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)

  ζ : ∣ ϕ ∣ ∘ ar ≡ b
  ζ = gfe (λ x → InvIsInv ∣ ϕ ∣(b x)(b∈Imf x))

  γ : (f ̂ 𝑩) b ≡ ∣ ϕ ∣((f ̂ 𝑨)(λ x → Inv ∣ ϕ ∣(b x)(b∈Imf x)))

  γ = (f ̂ 𝑩) b          ≡⟨ ap (f ̂ 𝑩)(ζ ⁻¹) ⟩
      (f ̂ 𝑩)(∣ ϕ ∣ ∘ ar)  ≡⟨(∥ ϕ ∥ f ar)⁻¹ ⟩
      ∣ ϕ ∣((f ̂ 𝑨) ar)   ∎
\end{code}

### Subalgebras

\begin{code}
_IsSubalgebraOf_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h 

SUBALGEBRA : {𝓤 𝓠 : Universe} → Algebra 𝓠 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓠 ⊔ 𝓤 ⁺ ̇
SUBALGEBRA {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOf 𝑨

subalgebra : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
subalgebra {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , 𝑩 IsSubalgebraOf 𝑨

Subalgebra : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Subalgebra {𝓤} = SUBALGEBRA {𝓤}{𝓤}

getSub : {𝓤 𝓠 : Universe}{𝑨 : Algebra 𝓠 𝑆} → SUBALGEBRA{𝓤}{𝓠} 𝑨 → Algebra 𝓤 𝑆
getSub SA = ∣ SA ∣
\end{code}

#### Example

The equalizer of two homomorphisms is a subuniverse.

\begin{code}
𝑬𝑯-is-subuniverse : {𝓤 : Universe} → funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}(g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
𝑬𝑯-is-subuniverse {𝓤} fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝓤}{𝑨}{𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑓}{𝑨}{𝑩} g h 𝒂 x
\end{code}

### Homomorphisms are determined on generating sets

\begin{code}
HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 𝑆}
            (X : Pred ∣ 𝑨 ∣ 𝓤)  (g h : hom 𝑨 𝑩)
 →          (∀ (x : ∣ 𝑨 ∣)  →  x ∈ X  →  ∣ g ∣ x ≡ ∣ h ∣ x)
            ---------------------------------------------
 →          (∀ (a : ∣ 𝑨 ∣) → a ∈ Sg 𝑨 X → ∣ g ∣ a ≡ ∣ h ∣ a)

HomUnique _ _ _ _ gx≡hx a (var x) = (gx≡hx) a x

HomUnique fe {𝑨}{𝑩} X g h gx≡hx a (app 𝑓 {𝒂} im𝒂⊆SgX) =
  ∣ g ∣ ((𝑓 ̂ 𝑨) 𝒂)     ≡⟨ ∥ g ∥ 𝑓 𝒂 ⟩
  (𝑓 ̂ 𝑩)(∣ g ∣ ∘ 𝒂 )   ≡⟨ ap (𝑓 ̂ 𝑩)(fe induction-hypothesis) ⟩
  (𝑓 ̂ 𝑩)(∣ h ∣ ∘ 𝒂)    ≡⟨ ( ∥ h ∥ 𝑓 𝒂 )⁻¹ ⟩
  ∣ h ∣ ((𝑓 ̂ 𝑨) 𝒂 )    ∎
 where induction-hypothesis = λ x → HomUnique fe {𝑨}{𝑩} X g h gx≡hx (𝒂 x) ( im𝒂⊆SgX x )
\end{code}

### Subalgebras of a class

\begin{code}
_IsSubalgebraOfClass_ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆)
 →                      Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓤 ⊔ 𝓠) ⁺ ̇
_IsSubalgebraOfClass_ {𝓤} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ SA ꞉ (SUBALGEBRA{𝓤} 𝑨) , (𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ SA ∣)

_is-subalgebra-of-class_ : {𝓤 𝓦 : Universe}(𝑩 : Algebra (𝓤 ⊔ 𝓦) 𝑆)
 →                      Pred (Algebra 𝓤 𝑆) (OV 𝓤) → (OV (𝓤 ⊔ 𝓦)) ̇
_is-subalgebra-of-class_ {𝓤}{𝓦} 𝑩 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , Σ SA ꞉ (subalgebra{𝓤}{𝓦} 𝑨) , (𝑨 ∈ 𝒦) × (𝑩 ≅ ∣ SA ∣)

SUBALGEBRAOFCLASS : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SUBALGEBRAOFCLASS {𝓤} 𝒦 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOfClass 𝒦

SubalgebraOfClass : {𝓤 𝓠 : Universe} → Pred (Algebra 𝓠 𝑆)(𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺) → 𝓞 ⊔ 𝓥 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SubalgebraOfClass {𝓤}{𝓠} = SUBALGEBRAOFCLASS {𝓤}{𝓠}{𝓞 ⊔ 𝓥 ⊔ 𝓠 ⁺}

getSubOfClass : {𝓤 𝓠 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) 𝓦} → SUBALGEBRAOFCLASS 𝒦 → Algebra 𝓤 𝑆
getSubOfClass SAC = ∣ SAC ∣

SUBALGEBRAOFCLASS' : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SUBALGEBRAOFCLASS' {𝓤}{𝓠} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓠 𝑆) , (𝑨 ∈ 𝒦) × SUBALGEBRA{𝓤}{𝓠} 𝑨
\end{code}

### Sugar

We use the convenient ≤ notation for the subalgebra relation.

\begin{code}
_≤_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨
\end{code}

### Subalgebra toolbox

\begin{code}
--Transitivity of IsSubalgebra (explicit args)
TRANS-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
 →         𝑩 ≤ 𝑨   →    𝑪 ≤ 𝑩
          ---------------------
 →              𝑪 ≤ 𝑨

TRANS-≤ 𝑨 𝑩 𝑪 BA CB =
 ∣ BA ∣ ∘ ∣ CB ∣ , ∘-embedding (fst ∥ BA ∥) (fst ∥ CB ∥) , ∘-hom 𝑪 𝑩 𝑨 {∣ CB ∣}{∣ BA ∣}(snd ∥ CB ∥) (snd ∥ BA ∥)

--Transitivity of IsSubalgebra (implicit args)
Trans-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →         𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑩 → 𝑪 ≤ 𝑨
Trans-≤ 𝑨 {𝑩} 𝑪 = TRANS-≤ 𝑨 𝑩 𝑪

--Transitivity of IsSubalgebra (implicit args)
trans-≤ : {𝓧 𝓨 𝓩 : Universe}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
 →         𝑩 ≤ 𝑨 → 𝑪 ≤ 𝑩 → 𝑪 ≤ 𝑨
trans-≤ {𝑨 = 𝑨}{𝑩 = 𝑩}{𝑪 = 𝑪} = TRANS-≤ 𝑨 𝑩 𝑪
transitivity-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}{𝑪 : Algebra 𝓩 𝑆}
 →         𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
transitivity-≤ 𝑨 {𝑩}{𝑪} A≤B B≤C = ∣ B≤C ∣ ∘ ∣ A≤B ∣ , ∘-embedding (fst ∥ B≤C ∥) (fst ∥ A≤B ∥) , ∘-hom 𝑨 𝑩 𝑪 {∣ A≤B ∣}{∣ B≤C ∣}(snd ∥ A≤B ∥) (snd ∥ B≤C ∥)

--Reflexivity of IsSubalgebra (explicit arg)
REFL-≤ : {𝓤 : Universe}(𝑨 : Algebra 𝓤 𝑆) → 𝑨 ≤ 𝑨
REFL-≤ 𝑨 = 𝑖𝑑 ∣ 𝑨 ∣ , id-is-embedding , id-is-hom

--Reflexivity of IsSubalgebra (implicit arg)
refl-≤ : {𝓤 : Universe}{𝑨 : Algebra 𝓤 𝑆} → 𝑨 ≤ 𝑨
refl-≤ {𝑨 = 𝑨} = REFL-≤ 𝑨

--Reflexivity of IsSubalgebra (explicit arg)
ISO-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆)(𝑩 : Algebra 𝓨 𝑆)(𝑪 : Algebra 𝓩 𝑆)
 →         𝑩 ≤ 𝑨   →   𝑪 ≅ 𝑩
          ---------------------
 →              𝑪 ≤ 𝑨
ISO-≤ 𝑨 𝑩 𝑪 B≤A C≅B = h , hemb , hhom
 where
  f : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
  f = fst ∣ C≅B ∣
  g : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  g = ∣ B≤A ∣
  h : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  h = g ∘ f

  hemb : is-embedding h
  hemb = ∘-embedding (fst ∥ B≤A ∥) (iso→embedding C≅B)

  hhom : is-homomorphism 𝑪 𝑨 h
  hhom = ∘-hom 𝑪 𝑩 𝑨 {f}{g} (snd ∣ C≅B ∣) (snd ∥ B≤A ∥)

Iso-≤ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →         𝑩 ≤ 𝑨 → 𝑪 ≅ 𝑩 → 𝑪 ≤ 𝑨
Iso-≤ 𝑨 {𝑩} 𝑪 = ISO-≤ 𝑨 𝑩 𝑪

iso-≤ : {𝓧 𝓨 𝓩 : Universe}{𝑨 : Algebra 𝓧 𝑆}{𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →         𝑩 ≤ 𝑨 → 𝑪 ≅ 𝑩 → 𝑪 ≤ 𝑨
iso-≤ {𝑨 = 𝑨} {𝑩 = 𝑩} 𝑪 = ISO-≤ 𝑨 𝑩 𝑪

trans-≤-≅ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →         𝑨 ≤ 𝑩 → 𝑨 ≅ 𝑪 → 𝑪 ≤ 𝑩
trans-≤-≅ {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} 𝑪 A≤B B≅C = ISO-≤ 𝑩 𝑨 𝑪 A≤B (sym-≅ B≅C)

TRANS-≤-≅ : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆)
 →         𝑨 ≤ 𝑩 → 𝑩 ≅ 𝑪 → 𝑨 ≤ 𝑪
TRANS-≤-≅ {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} 𝑪 A≤B B≅C = h , hemb , hhom
 where
  f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
  f = ∣ A≤B ∣
  g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣
  g = fst ∣ B≅C ∣

  h : ∣ 𝑨 ∣ → ∣ 𝑪 ∣
  h = g ∘ f

  hemb : is-embedding h
  hemb = ∘-embedding (iso→embedding B≅C)(fst ∥ A≤B ∥)

  hhom : is-homomorphism 𝑨 𝑪 h
  hhom = ∘-hom 𝑨 𝑩 𝑪 {f}{g} (snd ∥ A≤B ∥) (snd ∣ B≅C ∣) -- ISO-≤ 𝑨 𝑩 𝑪 A≤B B≅C

mono-≤ : {𝓤 𝓠 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆){𝒦 𝒦' : Pred (Algebra 𝓠 𝑆) 𝓦}
 →       𝒦 ⊆ 𝒦' → 𝑩 IsSubalgebraOfClass 𝒦 → 𝑩 IsSubalgebraOfClass 𝒦'
mono-≤ 𝑩 KK' KB = ∣ KB ∣ , fst ∥ KB ∥ , KK' (∣ snd ∥ KB ∥ ∣) , ∥ (snd ∥ KB ∥) ∥

lift-alg-is-sub : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} {𝑩 : Algebra 𝓤 𝑆}
 →           𝑩 IsSubalgebraOfClass 𝒦
 →           (lift-alg 𝑩 𝓤) IsSubalgebraOfClass 𝒦
lift-alg-is-sub {𝓤}{𝒦}{𝑩} (𝑨 , (sa , (KA , B≅sa))) = 𝑨 , sa , KA , trans-≅ _ _ _ (sym-≅ lift-alg-≅) B≅sa

lift-alg-lift-≤-lower : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →         𝑩 ≤ 𝑨 → (lift-alg 𝑩 𝓩) ≤ 𝑨
lift-alg-lift-≤-lower {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} B≤A = iso-≤{𝓧}{𝓨}{𝓩 = (𝓨 ⊔ 𝓩)}{𝑨}{𝑩} (lift-alg 𝑩 𝓩) B≤A (sym-≅ lift-alg-≅)

lift-alg-lower-≤-lift : {𝓧 𝓨 𝓩 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →                𝑩 ≤ 𝑨 → 𝑩 ≤ (lift-alg 𝑨 𝓩)
lift-alg-lower-≤-lift {𝓧}{𝓨}{𝓩} 𝑨 {𝑩} B≤A = γ
 where
  lA : Algebra (𝓧 ⊔ 𝓩) 𝑆
  lA = lift-alg 𝑨 𝓩

  A≅lA : 𝑨 ≅ lA
  A≅lA = lift-alg-≅

  f : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
  f = ∣ B≤A ∣

  g : ∣ 𝑨 ∣ → ∣ lA ∣
  g = ≅-map A≅lA

  h : ∣ 𝑩 ∣ → ∣ lA ∣
  h = g ∘ f

  hemb : is-embedding h
  hemb = ∘-embedding (≅-map-is-embedding A≅lA) (fst ∥ B≤A ∥)

  hhom : is-homomorphism 𝑩 lA h
  hhom = ∘-hom 𝑩 𝑨 lA {f}{g} (snd ∥ B≤A ∥) (snd ∣ A≅lA ∣)

  γ : 𝑩 IsSubalgebraOf lift-alg 𝑨 𝓩
  γ = h , hemb , hhom

lift-alg-sub-lift : {𝓤 𝓦 : Universe}(𝑨 : Algebra 𝓤 𝑆){𝑪 : Algebra (𝓤 ⊔ 𝓦) 𝑆}
 →                𝑪 ≤ 𝑨 → 𝑪 ≤ (lift-alg 𝑨 𝓦)
lift-alg-sub-lift {𝓤}{𝓦} 𝑨 {𝑪} C≤A = γ
 where
  lA : Algebra (𝓤 ⊔ 𝓦) 𝑆
  lA = lift-alg 𝑨 𝓦

  A≅lA : 𝑨 ≅ lA
  A≅lA = lift-alg-≅

  f : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
  f = ∣ C≤A ∣

  g : ∣ 𝑨 ∣ → ∣ lA ∣
  g = ≅-map A≅lA

  h : ∣ 𝑪 ∣ → ∣ lA ∣
  h = g ∘ f

  hemb : is-embedding h
  hemb = ∘-embedding (≅-map-is-embedding A≅lA) (fst ∥ C≤A ∥)

  hhom : is-homomorphism 𝑪 lA h
  hhom = ∘-hom 𝑪 𝑨 lA {f}{g} (snd ∥ C≤A ∥) (snd ∣ A≅lA ∣)

  γ : 𝑪 IsSubalgebraOf lift-alg 𝑨 𝓦
  γ = h , hemb , hhom

lift-alg-≤ lift-alg-lift-≤-lift : {𝓧 𝓨 𝓩 𝓦 : Universe}(𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}
 →         𝑨 ≤ 𝑩 → (lift-alg 𝑨 𝓩) ≤ (lift-alg 𝑩 𝓦)
lift-alg-≤ {𝓧}{𝓨}{𝓩}{𝓦} 𝑨 {𝑩} A≤B =
 transitivity-≤ lA {𝑩}{lB} (transitivity-≤ lA {𝑨}{𝑩} lA≤A A≤B) B≤lB
 where
  lA : Algebra (𝓧 ⊔ 𝓩) 𝑆
  lA = (lift-alg 𝑨 𝓩)
  lB : Algebra (𝓨 ⊔ 𝓦) 𝑆
  lB = (lift-alg 𝑩 𝓦)
  lA≤A :  lA ≤ 𝑨
  lA≤A = lift-alg-lift-≤-lower 𝑨 {𝑨} refl-≤
  B≤lB : 𝑩 ≤ lB
  B≤lB = lift-alg-lower-≤-lift 𝑩 {𝑩} refl-≤

lift-alg-lift-≤-lift = lift-alg-≤ -- (alias)
\end{code}

<!--
module mhe_subgroup_generalization {𝓦 : Universe} {𝑨 : Algebra 𝓦 𝑆} (ua : Univalence) where

 -- gfe : global-dfunext
 -- gfe = univalence-gives-global-dfunext ua

 op-closed : (∣ 𝑨 ∣ → 𝓦 ̇) → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ̇
 op-closed B = (f : ∣ 𝑆 ∣)(a : ∥ 𝑆 ∥ f → ∣ 𝑨 ∣)
  → ((i : ∥ 𝑆 ∥ f) → B (a i)) → B ((f ̂ 𝑨) a)

 subuniverse : 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 subuniverse = Σ B ꞉ (𝓟 ∣ 𝑨 ∣) , op-closed ( _∈₀ B)

 being-op-closed-is-subsingleton : (B : 𝓟 ∣ 𝑨 ∣)
  →           is-subsingleton (op-closed ( _∈₀ B ))
 being-op-closed-is-subsingleton B = Π-is-subsingleton gfe
  (λ f → Π-is-subsingleton gfe
   (λ a → Π-is-subsingleton gfe
    (λ _ → ∈₀-is-subsingleton B ((f ̂ 𝑨) a))))

 pr₁-is-embedding : is-embedding ∣_∣
 pr₁-is-embedding = pr₁-embedding being-op-closed-is-subsingleton

 --so equality of subalgebras is equality of their underlying
 --subsets in the powerset:
 ap-pr₁ : (B C : subuniverse) → B ≡ C → ∣ B ∣ ≡ ∣ C ∣
 ap-pr₁ B C = ap ∣_∣

 ap-pr₁-is-equiv : (B C : subuniverse) → is-equiv (ap-pr₁ B C)
 ap-pr₁-is-equiv =
  embedding-gives-ap-is-equiv ∣_∣ pr₁-is-embedding

 subuniverse-is-a-set : is-set subuniverse
 subuniverse-is-a-set B C = equiv-to-subsingleton
                           (ap-pr₁ B C , ap-pr₁-is-equiv B C)
                           (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)

 subuniverse-equality-gives-membership-equiv : (B C : subuniverse)
  →                                  B ≡ C
                      -----------------------------------
  →                   ( x : ∣ 𝑨 ∣ ) → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣)
 subuniverse-equality-gives-membership-equiv B C B≡C x =
  transport (λ - → x ∈₀ ∣ - ∣) B≡C ,
   transport (λ - → x ∈₀ ∣ - ∣ ) ( B≡C ⁻¹ )

 membership-equiv-gives-carrier-equality : (B C : subuniverse)
  →          ((x : ∣ 𝑨 ∣) →  x ∈₀ ∣ B ∣  ⇔  x ∈₀ ∣ C ∣)
            -----------------------------------------
  →                       ∣ B ∣ ≡ ∣ C ∣
 membership-equiv-gives-carrier-equality B C φ =
  subset-extensionality' ua α β
   where
    α :  ∣ B ∣ ⊆₀ ∣ C ∣
    α x = lr-implication (φ x)

    β : ∣ C ∣ ⊆₀ ∣ B ∣
    β x = rl-implication (φ x)

 membership-equiv-gives-subuniverse-equality : (B C : subuniverse)
  →            (( x : ∣ 𝑨 ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
               ---------------------------------------
  →                          B ≡ C
 membership-equiv-gives-subuniverse-equality B C =
  inverse (ap-pr₁ B C)
  (ap-pr₁-is-equiv B C)
     ∘ (membership-equiv-gives-carrier-equality B C)

 membership-equiv-is-subsingleton : (B C : subuniverse)
  →    is-subsingleton (( x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
 membership-equiv-is-subsingleton B C =
  Π-is-subsingleton gfe
   (λ x → ×-is-subsingleton
    (Π-is-subsingleton gfe (λ _ → ∈₀-is-subsingleton ∣ C ∣ x ))
      (Π-is-subsingleton gfe (λ _ → ∈₀-is-subsingleton ∣ B ∣ x )))

 subuniverse-equality : (B C : subuniverse)
  →    (B ≡ C)  ≃  ((x : ∣ 𝑨 ∣)  → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣))

 subuniverse-equality B C =
  logically-equivalent-subsingletons-are-equivalent _ _
    (subuniverse-is-a-set B C)
     (membership-equiv-is-subsingleton B C)
      (subuniverse-equality-gives-membership-equiv B C ,
        membership-equiv-gives-subuniverse-equality B C)

 carrier-equality-gives-membership-equiv : (B C : subuniverse)
  →                            ∣ B ∣ ≡ ∣ C ∣
                ----------------------------------------
  →              ( ( x : ∣ 𝑨 ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣ )
 carrier-equality-gives-membership-equiv B C (refl _) x = id , id

 --so we have...
 carrier-equiv : (B C : subuniverse)
  →   ((x : ∣ 𝑨 ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣) ≃ (∣ B ∣ ≡ ∣ C ∣)
 carrier-equiv B C =
  logically-equivalent-subsingletons-are-equivalent _ _
   (membership-equiv-is-subsingleton B C)
    (powersets-are-sets' ua ∣ B ∣ ∣ C ∣)
     (membership-equiv-gives-carrier-equality B C ,
       carrier-equality-gives-membership-equiv B C)

 -- ...which yields an alternative subuniverse equality lemma.
 subuniverse-equality' : (B C : subuniverse)
  →                      (B ≡ C) ≃ (∣ B ∣ ≡ ∣ C ∣)
 subuniverse-equality' B C =
  (subuniverse-equality B C) ● (carrier-equiv B C)

-->
