---
layout: default
title : UALib.Birkhoff.FreeAlgebra (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

[UALib.Birkhoff ↑](UALib.Birkhoff.html)

### <a id="relatively-free-algebra-types">Relatively Free Algebra Types</a>

This section presents the [UALib.Birkhoff.FreeAlgebra][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Birkhoff.FreeAlgebra
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where


open import UALib.Varieties.Preservation {𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}

### The free algebra

\begin{code}
module the-free-algebra {𝓤 𝓧 : Universe}{X : 𝓧 ̇} where

 -- H (𝑻 X)  (hom images of 𝑻 X)
 𝑻img : Pred (Algebra 𝓤 𝑆) (OV 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺ ̇
 𝑻img 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , Σ ϕ ꞉ hom (𝑻 X) 𝑨 , (𝑨 ∈ 𝒦) × Epic ∣ ϕ ∣

 -- Every algebra is a hom image of 𝑻 X.
 mkti : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}(𝑨 : Algebra 𝓤 𝑆)
  →     𝑨 ∈ 𝒦 → 𝑻img 𝒦
 mkti 𝑨 KA = (𝑨 , fst thg , KA , snd thg)
  where
   thg : Σ h ꞉ (hom (𝑻 X) 𝑨), Epic ∣ h ∣
   thg = 𝑻hom-gen 𝑨

 -- The algebra part of a hom image of 𝑻 X.
 𝑻𝑨 : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → 𝑻img 𝒦 → Algebra 𝓤 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 -- The hom part of a hom image of 𝑻 X.
 𝑻ϕ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))(ti : 𝑻img 𝒦)
  →   hom (𝑻 X) (𝑻𝑨 ti)
 𝑻ϕ _ ti = fst (snd ti)

 -- The part of a hom image of 𝑻 X that proves the hom is an epi.
 𝑻ϕE : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))(ti : 𝑻img 𝒦)
  →    Epic ∣ 𝑻ϕ 𝒦 ti ∣
 𝑻ϕE _ ti = snd (snd ∥ ti ∥)

 -- The collection of identities (p, q) satisfied by all subalgebras of algebras in 𝒦.
 ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (OV 𝓤)
 ψ  𝒦 (p , q) = ∀(𝑨 : Algebra 𝓤 𝑆) → (sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦)
                 →  ∣ lift-hom 𝑨 (fst(𝕏 𝑨)) ∣ p ≡ ∣ lift-hom 𝑨 (fst(𝕏 𝑨)) ∣ q

 ψRel : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Rel ∣ (𝑻 X) ∣ (OV 𝓤)
 ψRel 𝒦 p q = ψ 𝒦 (p , q)

 ψcompatible : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
  →            compatible (𝑻 X) (ψRel 𝒦)
 ψcompatible 𝒦 f {i} {j} iψj 𝑨 sA = γ
  where
   ti : 𝑻img (S{𝓤}{𝓤} 𝒦)
   ti = mkti 𝑨 sA

   ϕ : hom (𝑻 X) 𝑨
   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) ti

   γ : ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻 X) j)
   γ = ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡⟨ ∥ ϕ ∥ f i ⟩
       (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 sA)) ⟩
       (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
       ∣ ϕ ∣ ((f ̂ 𝑻 X) j) ∎

 ψRefl : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → reflexive (ψRel 𝒦)
 ψRefl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁

 ψSymm : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → symmetric (ψRel 𝒦)
 ψSymm p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

 ψTrans : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → transitive (ψRel 𝒦)
 ψTrans p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

 ψIsEquivalence : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → IsEquivalence (ψRel 𝒦)
 ψIsEquivalence = record { rfl = ψRefl ; sym = ψSymm ; trans = ψTrans }

 ψCon : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Congruence (𝑻 X)
 ψCon 𝒦 = mkcon (ψRel 𝒦) (ψcompatible 𝒦) ψIsEquivalence
\end{code}

### Properties of ψ

\begin{code}
 𝑻i⊧ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
        (𝑪 : Algebra 𝓤 𝑆) (sC : 𝑪 ∈ S{𝓤}{𝓤} 𝒦)
        (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ ψ 𝒦
       --------------------------------------------------
  →     ∣ 𝑻ϕ (S 𝒦)(mkti 𝑪 sC) ∣ p ≡ ∣ 𝑻ϕ (S 𝒦)(mkti 𝑪 sC) ∣ q

 𝑻i⊧ψ 𝒦 𝑪 sC p q pψq = pψq 𝑪 sC
\end{code}

Recall, `mkti X 𝑨 sC` has type `𝑻img X (S 𝒦)` and consists of a quadruple:

```agda
(𝑨 , ϕ , sA , ϕE),
```

where

```agda
𝑨 : Algebra 𝓤 𝑆 , ϕ : hom (𝑻 X) 𝑨 , sA : 𝑨 ∈ S 𝒦 , ϕE : Epic ∣ ϕ ∣
```

Lemma 4.27. (Bergman) Let 𝒦 be a class of algebras, and ψCon defined as above.
                     Then 𝔽 := 𝑻 / ψCon is isomorphic to an algebra in SP(𝒦).

Proof. 𝔽 ↪ ⨅ 𝒜, where 𝒜 = {𝑨 / θ : 𝑨 / θ ∈ S 𝒦}.
       Therefore, 𝔽 ≅ 𝑩, where 𝑩 is a subalgebra of ⨅ 𝒜 ∈ PS(𝒦).
       Thus 𝔽 is isomorphic to an algebra in SPS(𝒦).
       By SPS⊆SP, 𝔽 is isomorphic to an algebra in SP(𝒦).


### The relatively free algebra

The free algebra in a variety, or "relatively free algebra" (relative to the variety), is the quotient of the free algebra modulo the congruence generated by the set of identities satisfied by all algebras in the variety.  We will denote the relatively free algebra by 𝔉 or 𝔽 and construct it as follows.

\begin{code}
open the-free-algebra

module the-relatively-free-algebra
 {𝓤 𝓧 : Universe}{X : 𝓧 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} where

 𝓕 : Universe -- (universe level of the relatively free algebra)
 𝓕 = (𝓧 ⊔ (OV 𝓤))⁺

 𝔉 : Algebra 𝓕 𝑆
 𝔉 =  𝑻 X ╱ (ψCon 𝒦)
\end{code}

The domain, ∣ 𝔉 ∣, is defined by

```agda
( ∣ 𝑻 X ∣ /ₚ ⟨ θ ⟩ ) = Σ C ꞉ _ ,  Σ p ꞉ ∣ 𝑻 X ∣ ,  C ≡ ( [ p ] ≈ )
```

which is the collection { C : ∃ p ∈ ∣ 𝑻 X ∣, C ≡ [ p ] } of θ-classs of 𝑻 X.
\begin{code}
 𝔉-free-lift : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
               (h₀ : X → ∣ 𝑨 ∣)  →  ∣ 𝔉 ∣ → ∣ 𝑨 ∣

 𝔉-free-lift {𝓦}𝑨 h₀ (_ , x , _) = (free-lift{𝓧}{𝓦} 𝑨 h₀) x

 𝔉-free-lift-interpretation : (𝑨 : Algebra 𝓤 𝑆)
                              (h₀ : X → ∣ 𝑨 ∣)(𝒙 : ∣ 𝔉 ∣)
                             -------------------------------------
  →                           (⌜ 𝒙 ⌝ ̇ 𝑨) h₀ ≡ 𝔉-free-lift 𝑨 h₀ 𝒙

 𝔉-free-lift-interpretation 𝑨 f 𝒙 = free-lift-interpretation 𝑨 f ⌜ 𝒙 ⌝


 𝔉-lift-hom : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
               (h₀ : X → ∣ 𝑨 ∣) → hom 𝔉 𝑨

 𝔉-lift-hom 𝑨 h₀ = f , fhom
  where
   f : ∣ 𝔉 ∣ → ∣ 𝑨 ∣
   f = 𝔉-free-lift 𝑨 h₀

   ϕ : hom (𝑻 X) 𝑨
   ϕ = lift-hom 𝑨 h₀

   fhom : is-homomorphism 𝔉 𝑨 f
   fhom 𝑓 𝒂 = ∥ ϕ ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝  )

 𝔉-lift-agrees-on-X : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
                       (h₀ : X → ∣ 𝑨 ∣)(x : X)
                     -----------------------------------------
  →                    h₀ x ≡ ( ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ ℊ x ⟧ )

 𝔉-lift-agrees-on-X _ h₀ x = 𝓇ℯ𝒻𝓁

 𝔉-lift-of-epic-is-epic : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
                           (h₀ : X → ∣ 𝑨 ∣)  →  Epic h₀
                          --------------------------------
  →                        Epic ∣ 𝔉-lift-hom 𝑨 h₀ ∣

 𝔉-lift-of-epic-is-epic 𝑨 h₀ hE y = γ
  where
   h₀pre : Image h₀ ∋ y
   h₀pre = hE y

   h₀⁻¹y : X
   h₀⁻¹y = Inv h₀ y (hE y)

   η : y ≡ ( ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ ℊ (h₀⁻¹y) ⟧ )
   η = y                               ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
       h₀ h₀⁻¹y                         ≡⟨ (𝔉-lift-agrees-on-X) 𝑨 h₀ h₀⁻¹y ⟩
       ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ (ℊ h₀⁻¹y) ⟧ ∎

   γ : Image ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ∋ y
   γ = eq y (⟦ ℊ h₀⁻¹y ⟧) η


 𝑻-canonical-projection : (θ : Congruence{OV 𝓧}{𝓤} (𝑻 X)) → epi (𝑻 X) ((𝑻 X) ╱ θ)
 𝑻-canonical-projection θ = canonical-projection (𝑻 X) θ

 𝔉-canonical-projection : epi (𝑻 X) 𝔉
 𝔉-canonical-projection = canonical-projection (𝑻 X) (ψCon 𝒦)

 π𝔉 : hom (𝑻 X) 𝔉
 π𝔉 = epi-to-hom (𝑻 X) {𝔉} 𝔉-canonical-projection

 π𝔉-X-defined : (g : hom (𝑻 X) 𝔉)
  →              ((x : X) → ∣ g ∣ (ℊ x) ≡ ⟦ ℊ x ⟧)
  →              (t : ∣ 𝑻 X ∣ )
               ---------------------------------
  →               ∣ g ∣ t ≡ ⟦ t ⟧

 π𝔉-X-defined g gx t = free-unique gfe 𝔉 g π𝔉 gπ𝔉-agree-on-X t
  where
   gπ𝔉-agree-on-X : ((x : X) → ∣ g ∣ (ℊ x) ≡ ∣ π𝔉 ∣ ( ℊ x ))
   gπ𝔉-agree-on-X x = gx x


 X↪𝔉 : X → ∣ 𝔉 ∣
 X↪𝔉 x = ⟦ ℊ x ⟧


 ψlem : (p q : ∣ 𝑻 X ∣ )
  →     ∣ lift-hom 𝔉 X↪𝔉 ∣ p ≡ ∣ lift-hom 𝔉 X↪𝔉 ∣ q
       -----------------------------------------------
  →                (p , q) ∈ ψ 𝒦

 ψlem p q gpgq 𝑨 sA = γ
   where
    g : hom (𝑻 X) 𝔉
    g = lift-hom 𝔉 (X↪𝔉)

    h₀ : X → ∣ 𝑨 ∣
    h₀ = fst (𝕏 𝑨)

    f : hom 𝔉 𝑨
    f = 𝔉-lift-hom 𝑨 h₀

    h ϕ : hom (𝑻 X) 𝑨
    h = HomComp (𝑻 X) 𝑨 g f
    ϕ = 𝑻ϕ (S 𝒦) (mkti 𝑨 sA)

     --(homs from 𝑻 X to 𝑨 that agree on X are equal)
    lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ ℊ x ⟧
    lift-agreement x = 𝔉-lift-agrees-on-X 𝑨 h₀ x
    fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
    fgx≡ϕ x = (lift-agreement x)⁻¹
    h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
    h≡ϕ t = free-unique gfe 𝑨 h ϕ fgx≡ϕ t

    γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
    γ = ∣ ϕ ∣ p ≡⟨ (h≡ϕ p)⁻¹ ⟩ (∣ f ∣ ∘ ∣ g ∣) p
               ≡⟨ 𝓇ℯ𝒻𝓁 ⟩ ∣ f ∣ ( ∣ g ∣ p )
               ≡⟨ ap ∣ f ∣ gpgq ⟩ ∣ f ∣ ( ∣ g ∣ q )
               ≡⟨ h≡ϕ q ⟩ ∣ ϕ ∣ q ∎

\end{code}

----------------------------

{% include UALib.Links.md %}

