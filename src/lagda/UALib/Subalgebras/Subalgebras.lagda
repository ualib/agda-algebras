---
layout: default
title : UALib.Subalgebras.Subalgebras module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

[UALib.Subalgebras ↑](UALib.Subalgebras.html)

### <a id="subalgebra-types">Subalgebra Types</a>

This section presents the [UALib.Subalgebras.Subalgebras][] module of the [Agda Universal Algebra Library][].

Here we define a subalgebra of an algebra as well as the collection of all subalgebras of a given class of algebras.

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


_IsSubalgebraOf_ : {𝓤 𝓦 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓦 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h 

SUBALGEBRA : {𝓤 𝓦 : Universe} → Algebra 𝓦 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤 ⁺ ̇
SUBALGEBRA {𝓤} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓤 𝑆) , 𝑩 IsSubalgebraOf 𝑨

subalgebra : {𝓤 𝓦 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ⁺ ̇
subalgebra {𝓤}{𝓦} 𝑨 = Σ 𝑩 ꞉ (Algebra 𝓦 𝑆) , 𝑩 IsSubalgebraOf 𝑨

Subalgebra : {𝓤 : Universe} → Algebra 𝓤 𝑆 → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
Subalgebra {𝓤} = SUBALGEBRA {𝓤}{𝓤}

getSub : {𝓤 𝓦 : Universe}{𝑨 : Algebra 𝓦 𝑆} → SUBALGEBRA{𝓤}{𝓦} 𝑨 → Algebra 𝓤 𝑆
getSub SA = ∣ SA ∣
\end{code}


#### Example

The equalizer of two homomorphisms is a subuniverse.

\begin{code}
𝑬𝑯-is-subuniverse : {𝓤 𝓦 : Universe} → funext 𝓥 𝓦 →
                    {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra 𝓦 𝑆}
                    (g h : hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}

𝑬𝑯-is-subuniverse fe {𝑨} {𝑩} g h = mksub (𝑬𝑯 {𝑩 = 𝑩} g h) λ 𝑓 𝒂 x → 𝑬𝑯-is-closed fe {𝑨}{𝑩} g h {𝑓} 𝒂 x
\end{code}

Observe that the type universe level 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ arises quite often throughout the ualib since it is the level of the type `Algebra 𝓤 𝑆` of an algebra in the signature 𝑆 and domain of type 𝓤 ̇.  Let us define, once and for all, a simple notation for this universe level.

\begin{code}
OV : Universe → Universe
OV 𝓤 = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
\end{code}

So, hereinafter, we typically write `OV 𝓤` in place of the more cumbersome 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺.

#### Subalgebras of a class

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

getSubOfClass : {𝓤 𝓠 𝓦 : Universe}{𝒦 : Pred (Algebra 𝓠 𝑆) 𝓦} → SUBALGEBRAOFCLASS 𝒦 → Algebra 𝓤 𝑆
getSubOfClass SAC = ∣ SAC ∣

SUBALGEBRAOFCLASS' : {𝓤 𝓠 𝓦 : Universe} → Pred (Algebra 𝓠 𝑆) 𝓦 → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ (𝓠 ⊔ 𝓤) ⁺ ̇
SUBALGEBRAOFCLASS' {𝓤}{𝓠} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓠 𝑆) , (𝑨 ∈ 𝒦) × SUBALGEBRA{𝓤}{𝓠} 𝑨
\end{code}

##### Syntactic sugar

We use the convenient ≤ notation for the subalgebra relation.

\begin{code}
_≤_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
𝑩 ≤ 𝑨 = 𝑩 IsSubalgebraOf 𝑨
\end{code}


#### Subalgebra lemmata

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
