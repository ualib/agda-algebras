---
layout: default
title : birkhoff module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

<!--
FILE: birkhoff.agda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 12 Jan 2021
-->

## Birkhoff's Variety Theorem

### Options, imports

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import basic
open import prelude using (global-dfunext; _↪_)

module birkhoff
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import congruences {𝑆 = 𝑆}{gfe}
open import homomorphisms {𝑆 = 𝑆}{gfe}
open import terms {𝑆 = 𝑆}{gfe}{𝕏} renaming (generator to ℊ)
open import subuniverses {𝑆 = 𝑆}{gfe}{𝕏}
open import closure {𝑆 = 𝑆}{gfe}{𝕏}

open relation-predicate-classes
open congruence-predicates
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

We define it as follows.

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

### The proof of Birkhoff's HSP theorem

\begin{code}
module proof-of-birkhoff
 {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 {X : 𝓤 ̇}
 -- extensionality assumptions:
           {hfe : hfunext (OV 𝓤)(OV 𝓤)}
           {pe : propext (OV 𝓤)}
           {ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q)}
           {ssA : ∀ C → is-subsingleton (𝒜{OV 𝓤}{OV 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C)}
 where

 open relation-predicate-classes
 open congruence-predicates
 open class-product-inclusions {𝓤 = 𝓤}{𝒦 = 𝒦}
 open class-product {𝓤 = 𝓤}{𝑆 = 𝑆}{𝒦 = 𝒦}
 open the-relatively-free-algebra{𝓤}{𝓤}{X}{𝒦}

 -- NOTATION.
 ovu ovu+ ovu++ : Universe
 ovu = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
 ovu+ = ovu ⁺
 ovu++ = ovu ⁺ ⁺
\end{code}

Next we prove the lift-alg-V-closure lemma, which says that if an algebra 𝑨 belongs to the variety 𝕍, then so does its lift.  This dispenses with annoying universe level problems that arise later---a minor techinical issue, but the proof is long and tedious, not to mention uninteresting.

\begin{code}

 open Lift
 lift-alg-V-closure -- (alias)
  VlA : {𝑨 : Algebra ovu 𝑆}
   →     𝑨 ∈ V{𝓤}{ovu} 𝒦
       ---------------------------------
   →    lift-alg 𝑨 ovu+ ∈ V{𝓤}{ovu+} 𝒦

 VlA (vbase{𝑨} x) = visow (vbase{𝓤}{𝓦 = ovu+} x) A≅B
  where
   A≅B : lift-alg 𝑨 ovu+ ≅ lift-alg (lift-alg 𝑨 ovu) ovu+
   A≅B = lift-alg-associative 𝑨

 VlA (vlift{𝑨} x) = visow (vlift{𝓤}{𝓦 = ovu+} x) A≅B
  where
   A≅B : lift-alg 𝑨 ovu+ ≅ lift-alg (lift-alg 𝑨 ovu) ovu+
   A≅B = lift-alg-associative 𝑨

 VlA (vliftw{𝑨} x) = visow (VlA x) A≅B
  where
   A≅B : (lift-alg 𝑨 ovu+) ≅ lift-alg (lift-alg 𝑨 ovu) ovu+
   A≅B = lift-alg-associative 𝑨

 VlA (vhimg{𝑨}{𝑩} x hB) = vhimg (VlA x) (lift-alg-hom-image hB)

 VlA (vssub{𝑨}{𝑩} x B≤A) = vssubw (vlift x) lB≤lA
  where
   lB≤lA : lift-alg 𝑩 ovu+ ≤ lift-alg 𝑨 ovu+
   lB≤lA = lift-alg-≤ 𝑩{𝑨} B≤A

 VlA (vssubw{𝑨}{𝑩} x B≤A) = vssubw vlA lB≤lA
  where
   vlA : (lift-alg 𝑨 ovu+) ∈ V{𝓤}{ovu+} 𝒦
   vlA = VlA x

   lB≤lA : (lift-alg 𝑩 ovu+) ≤ (lift-alg 𝑨 ovu+)
   lB≤lA = lift-alg-≤ 𝑩{𝑨} B≤A

 VlA (vprodu{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
  where
   𝑰 : ovu+ ̇
   𝑰 = Lift{ovu}{ovu+} I

   lA+ : Algebra ovu+ 𝑆
   lA+ = lift-alg (⨅ 𝒜) ovu+

   lA : 𝑰 → Algebra ovu+ 𝑆
   lA i = lift-alg (𝒜 (lower i)) ovu+

   vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{ovu+} 𝒦
   vlA i = vlift (x (lower i))

   iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
   iso-components i = lift-alg-≅

   B≅A : lA+ ≅ ⨅ lA
   B≅A = lift-alg-⨅≅ gfe iso-components

 VlA (vprodw{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
  where
   𝑰 : ovu+ ̇
   𝑰 = Lift{ovu}{ovu+} I

   lA+ : Algebra ovu+ 𝑆
   lA+ = lift-alg (⨅ 𝒜) ovu+

   lA : 𝑰 → Algebra ovu+ 𝑆
   lA i = lift-alg (𝒜 (lower i)) ovu+

   vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{ovu+} 𝒦
   vlA i = VlA (x (lower i))

   iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
   iso-components i = lift-alg-≅

   B≅A : lA+ ≅ ⨅ lA
   B≅A = lift-alg-⨅≅ gfe iso-components

 VlA (visou{𝑨}{𝑩} x A≅B) = visow (vlift x) lA≅lB
  where
   lA≅lB : (lift-alg 𝑨 ovu+) ≅ (lift-alg 𝑩 ovu+)
   lA≅lB = lift-alg-iso 𝓤 ovu+ 𝑨 𝑩 A≅B

 VlA (visow{𝑨}{𝑩} x A≅B) = visow vlA lA≅lB
  where
   lA lB : Algebra ovu+ 𝑆
   lA = lift-alg 𝑨 ovu+
   lB = lift-alg 𝑩 ovu+

   vlA : lA ∈ V{𝓤}{ovu+} 𝒦
   vlA = VlA x

   lA≅lB : lA ≅ lB
   lA≅lB = lift-alg-iso ovu ovu+ 𝑨 𝑩 A≅B

 lift-alg-V-closure = VlA -- (alias)


\end{code}

Next we formalize the obvious fact that SP(𝒦) ⊆ V(𝒦). Unfortunately, the formal proof is neither trivial nor interesting.

\begin{code}

 SP⊆V' : S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦) ⊆ V{𝓤}{ovu+} 𝒦

 SP⊆V' (sbase{𝑨} x) = γ
  where
   llA lA+ : Algebra ovu+ 𝑆
   lA+ = lift-alg 𝑨 ovu+
   llA = lift-alg (lift-alg 𝑨 ovu) ovu+

   vllA : llA ∈ V{𝓤}{ovu+} 𝒦
   vllA = lift-alg-V-closure (SP⊆V (sbase x))

   llA≅lA+ : llA ≅ lA+
   llA≅lA+ = sym-≅ (lift-alg-associative 𝑨)

   γ : lA+ ∈ (V{𝓤}{ovu+} 𝒦)
   γ = visow vllA llA≅lA+

 SP⊆V' (slift{𝑨} x) = lift-alg-V-closure (SP⊆V x)

 SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw vlA B≤lA
  where
   lA : Algebra ovu+ 𝑆
   lA = lift-alg 𝑨 ovu+

   vlA : lA ∈ V{𝓤}{ovu+} 𝒦
   vlA = lift-alg-V-closure (SP⊆V spA)

   B≤lA : 𝑩 ≤ lA
   B≤lA = (lift-alg-lower-≤-lift {ovu}{ovu+}{ovu+} 𝑨 {𝑩}) B≤A

 SP⊆V' (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V' spA) B≤A

 SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (lift-alg-V-closure vA) lA≅B
  where
   lA : Algebra ovu+ 𝑆
   lA = lift-alg 𝑨 ovu+

   plA : 𝑨 ∈ S{ovu}{ovu}(P{𝓤}{ovu} 𝒦)
   plA = x

   vA : 𝑨 ∈ V{𝓤}{ovu} 𝒦
   vA = SP⊆V x

   lA≅B : lA ≅ 𝑩
   lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B
\end{code}

Now we come to a step in the Agda formalization of Birkhoff's theorem that turned out to be surprisingly nontrivial---namely, the proof that the relatively free algebra 𝔽 embeds in the product ℭ of all subalgebras of algebras in the given class 𝒦.  To prepare for this battle, we arm ourselves with a small arsenal of notations and definitions.

\begin{code}
 open Congruence

 -- NOTATION.

 -- 𝔽 is the relatively free algebra
 𝔽 : Algebra ovu+ 𝑆
 𝔽 = 𝔉 -- 𝒦

 -- 𝕍 is HSP(𝒦)
 𝕍 : Pred (Algebra ovu+ 𝑆) ovu++
 𝕍 = V{𝓤}{ovu+} 𝒦

 ℑs : ovu ̇
 ℑs = ℑ (S{𝓤}{𝓤} 𝒦)

 𝔄s : ℑs → Algebra 𝓤 𝑆
 𝔄s = λ (i : ℑs) → ∣ i ∣

 SK𝔄 : (i : ℑs) → (𝔄s i) ∈ S{𝓤}{𝓤} 𝒦
 SK𝔄 = λ (i : ℑs) → ∥ i ∥

 -- ℭ is the product of all subalgebras of 𝒦.
 ℭ : Algebra ovu 𝑆
 ℭ = ⨅ 𝔄s
 -- elements of ℭ are mappings from ℑs to {𝔄s i : i ∈ ℑs}
 𝔥₀ : X → ∣ ℭ ∣
 𝔥₀ x = λ i → (fst (𝕏 (𝔄s i))) x -- fst (𝕏 ℭ)
                         --                             𝔄1
 ϕ𝔠 : hom (𝑻 X) ℭ        --                            77
 ϕ𝔠 = lift-hom ℭ 𝔥₀      --                           /
                         --        𝑻 -----ϕ≡h --->>  ℭ -->> 𝔄2
 𝔤 : hom (𝑻 X) 𝔽         --         \             77        ⋮
 𝔤 = lift-hom 𝔽 (X↪𝔉)   --          \           /
                          --          g         ∃f
 𝔣 : hom 𝔽 ℭ              --           \       /
 𝔣 = 𝔉-free-lift ℭ 𝔥₀ ,    --            \    /
     λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝) --    V l/
                           --            𝔽= 𝑻/ψ

 𝔤-⟦⟧ : ∀ p → ∣ 𝔤 ∣ p ≡ ⟦ p ⟧
 𝔤-⟦⟧ p = π𝔉-X-defined 𝔤 (𝔉-lift-agrees-on-X 𝔉 X↪𝔉) p

 --Projection out of the product ℭ onto the specified (i-th) factor.
 𝔭 : (i : ℑs) → ∣ ℭ ∣ → ∣ 𝔄s i ∣
 𝔭 i 𝒂 = 𝒂 i

 𝔭hom : (i : ℑs) → hom ℭ (𝔄s i)
 𝔭hom = ⨅-projection-hom {I = ℑs}{𝒜 = 𝔄s}

 -- the composition:  𝔽 --∣ 𝔣 ∣-->  ℭ --(𝔭 i)--> 𝔄s i
 𝔭𝔣 : ∀ i → ∣ 𝔽 ∣ → ∣ 𝔄s i ∣
 𝔭𝔣 i = (𝔭 i) ∘ ∣ 𝔣 ∣

 𝔭𝔣hom : (i : ℑs) → hom 𝔽 (𝔄s i)
 𝔭𝔣hom i = HomComp 𝔽 (𝔄s i) 𝔣 (𝔭hom i)

 𝔭ϕ𝔠 : ∀ i → ∣ 𝑻 X ∣ → ∣ 𝔄s i ∣
 𝔭ϕ𝔠 i = ∣ 𝔭hom i ∣ ∘ ∣ ϕ𝔠 ∣

 𝔓 : ∀ i → hom (𝑻 X) (𝔄s i)
 𝔓 i = HomComp (𝑻 X) (𝔄s i) ϕ𝔠 (𝔭hom i)

 𝔭ϕ𝔠≡𝔓 : ∀ i p → (𝔭ϕ𝔠 i) p ≡ ∣ 𝔓 i ∣ p
 𝔭ϕ𝔠≡𝔓 i p = 𝓇ℯ𝒻𝓁

 -- The class of subalgebras of products of 𝒦.
 SP𝒦 : Pred (Algebra (ovu) 𝑆) (OV (ovu))
 SP𝒦 = S{ovu}{ovu}(P{𝓤}{ovu} 𝒦)
\end{code}

Armed with these tools, we proceed to the proof that the free algebra 𝔽 is a subalgebra of the product ℭ of all subalgebras of algebras in 𝒦.  The hard part of the proof is showing that `𝔣 : hom 𝔽 ℭ` is a monomorphism. Let's dispense with that first.

\begin{code}
 Ψ : Rel ∣ 𝑻 X ∣ (OV 𝓤)
 Ψ = ψRel 𝒦

 mon𝔣 : Monic ∣ 𝔣 ∣
 mon𝔣 (.(Ψ p) , p , refl _) (.(Ψ q) , q , refl _) fpq = γ
  where

   pΨq : Ψ p q
   pΨq 𝑨 sA = γ'
    where
     𝔭A : hom 𝔽 𝑨
     𝔭A = 𝔭𝔣hom (𝑨 , sA)

     𝔣pq : ∣ 𝔭A ∣ ⟦ p ⟧ ≡ ∣ 𝔭A ∣ ⟦ q ⟧
     𝔣pq = ∣ 𝔭A ∣ ⟦ p ⟧                    ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ p ⟧ ) ≡⟨ ap (λ - → (∣ 𝔭hom (𝑨 , sA) ∣ -)) fpq ⟩
          ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ q ⟧ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ 𝔭A ∣ ⟦ q ⟧                     ∎

     h₀ : X → ∣ 𝑨 ∣
     h₀ =  (𝔭 (𝑨 , sA)) ∘ 𝔥₀

     h ϕ : hom (𝑻 X) 𝑨
     h = HomComp (𝑻 X) 𝑨 𝔤 𝔭A

     ϕ = lift-hom 𝑨 h₀

     --(homs from 𝑻 X to 𝑨 that agree on X are equal)
     lift-agreement : (x : X) → h₀ x ≡ ∣ 𝔭A ∣ ⟦ ℊ x ⟧
     lift-agreement x = 𝔉-lift-agrees-on-X 𝑨 h₀ x

     𝔣gx≡ϕ : (x : X) → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
     𝔣gx≡ϕ x = (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) (ℊ x)         ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
                ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ (ℊ x) )       ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ (ℊ x)) ⟩
                ∣ 𝔭A ∣ (⟦ ℊ x ⟧)            ≡⟨ (lift-agreement x)⁻¹ ⟩
                 h₀ x                      ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
                ∣ ϕ ∣ (ℊ x) ∎

     h≡ϕ' : ∀ t → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) t ≡ ∣ ϕ ∣ t
     h≡ϕ' t = free-unique gfe 𝑨 h ϕ 𝔣gx≡ϕ t

     SPu : Pred (Algebra 𝓤 𝑆) (OV 𝓤)
     SPu = S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
     i : ℑs
     i = (𝑨 , sA)
     𝔄i : Algebra 𝓤 𝑆
     𝔄i = 𝔄s i
     sp𝔄i : 𝔄i ∈ SPu
     sp𝔄i = S⊆SP{𝓤}{𝓤} sA

     γ' : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
     γ' = ∣ ϕ ∣ p              ≡⟨ (h≡ϕ' p)⁻¹ ⟩
          (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) p   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ p )   ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ p) ⟩
          ∣ 𝔭A ∣ ⟦ p ⟧         ≡⟨ 𝔣pq ⟩
          ∣ 𝔭A ∣ ⟦ q ⟧         ≡⟨ (ap ∣ 𝔭A ∣ (𝔤-⟦⟧ q))⁻¹ ⟩
          ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ q )   ≡⟨ h≡ϕ' q ⟩
          ∣ ϕ ∣ q              ∎

   γ : ( Ψ p , p , 𝓇ℯ𝒻𝓁) ≡ ( Ψ q , q , 𝓇ℯ𝒻𝓁)
   γ = class-extensionality' pe gfe ssR ssA ψIsEquivalence pΨq

\end{code}
With that out of the way, the proof that 𝔽 is (isomorphic to) a subalgebra of ℭ is all but complete.

\begin{code}
 𝔽≤ℭ : is-set ∣ ℭ ∣ → 𝔽 ≤ ℭ
 𝔽≤ℭ Cset = ∣ 𝔣 ∣ , (emb𝔣 , ∥ 𝔣 ∥)
  where
   emb𝔣 : is-embedding ∣ 𝔣 ∣
   emb𝔣 = monic-into-set-is-embedding Cset ∣ 𝔣 ∣ mon𝔣
\end{code}
With this result in hand, along with the results we proved early---namely, that PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ 𝕍---it is not hard to show that 𝔽 belongs to SP(𝒦), and hence to 𝕍.

\begin{code}
 𝔽∈SP : is-set ∣ ℭ ∣ → 𝔽 ∈ (S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦))
 𝔽∈SP Cset = ssub spC (𝔽≤ℭ Cset)
  where
   spC : ℭ ∈ (S{ovu}{ovu} (P{𝓤}{ovu} 𝒦))
   spC = (class-prod-s-∈-sp hfe)

 𝔽∈𝕍 : is-set ∣ ℭ ∣ → 𝔽 ∈ 𝕍
 𝔽∈𝕍 Cset = SP⊆V' (𝔽∈SP Cset)
\end{code}

And with that we are well positioned to complete the formal proof of Birkhoff's celebrated result that every variety is defined by a set of identities; that is, every variety is an "equational class."

\begin{code}
 -- Birkhoff's theorem: every variety is an equational class.
 birkhoff : is-set ∣ ℭ ∣ → Mod X (Th 𝕍) ⊆ 𝕍

 birkhoff Cset {𝑨} MThVA = γ
  where
   T : Algebra (OV 𝓤) 𝑆
   T = 𝑻 X

   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst (𝕏 𝑨)

   h₀E : Epic h₀
   h₀E = snd (𝕏 𝑨)

   ϕ : Σ h ꞉ (hom 𝔽 𝑨) , Epic ∣ h ∣
   ϕ = (𝔉-lift-hom 𝑨 h₀) , 𝔉-lift-of-epic-is-epic 𝑨 h₀ h₀E

   AiF : 𝑨 is-hom-image-of 𝔽
   AiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) ) , refl-≅

   γ : 𝑨 ∈ 𝕍
   γ = vhimg (𝔽∈𝕍 Cset) AiF
\end{code}

Some readers (and coders) familiar with Birkhoff's theorem might worry that we haven't acheived our goal because they may be used to seeing it presented as an "if and only if" assertion.  Those fears are quickly put to rest. Indeed, the converse of the result just proved is that every equational class is closed under HSP, but we already proved that, formally of course, in the closure module. Indeed, there it is proved that H, S, and P preserve identities.

