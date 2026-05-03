---
layout: default
title : "Base.Homomorphisms.Noether module (The Agda Universal Algebra Library)"
date : "2021-01-13"
author: "agda-algebras development team"
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This is the [Base.Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].


```agda


{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Legacy.Base.Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ---------------------------------------
open  import Data.Product     using ( Σ-syntax ; _,_ ; _×_ )
                              renaming ( proj₁ to fst ; proj₂ to snd )
open  import Function         using ( _∘_ ; id )
open  import Level            using (Level )
open  import Relation.Binary  using ( IsEquivalence )

open  import Relation.Binary.PropositionalEquality as ≡
      using ( module ≡-Reasoning ; _≡_ )

-- Imports from agda-algebras --------------------------------------------------------------
open import Legacy.Base.Relations         using ( ⌞_⌟ ; mkblk ; ⟪_⟫ )
open import Overture               using ( ∣_∣ ; ∥_∥ ; _⁻¹ )
open import Legacy.Base.Functions         using ( Image_∋_ ; IsInjective ; SurjInv )
                                   using ( IsSurjective ; SurjInvIsInverseʳ )

open import Legacy.Base.Algebras {𝑆 = 𝑆}  using ( Algebra ; _̂_ ; Con ; IsCongruence )

open  import Legacy.Base.Homomorphisms.Kernels {𝑆 = 𝑆}
      using ( kercon ; ker[_⇒_]_↾_ ; πker )

open  import Legacy.Base.Equality
      using ( swelldef ; is-set ; blk-uip ; is-embedding ; monic-is-embedding|Set )
      using ( pred-ext ; block-ext|uip )

open  import Legacy.Base.Homomorphisms.Basic {𝑆 = 𝑆}
      using ( hom ; is-homomorphism ; epi ; epi→hom )

private variable α β γ : Level
```



#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

Here we formalize a version of the *first homomorphism theorem*, sometimes called
*Noether's first homomorphism theorem*, after Emmy Noether who was among the first
proponents of the abstract approach to the subject that we now call "modern algebra").

Informally, the theorem states that every homomorphism from `𝑨` to `𝑩` (`𝑆`-algebras)
factors through the quotient algebra `𝑨 ╱ ker h` (`𝑨` modulo the kernel of the given
homomorphism).  In other terms, given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩`
which, when composed with the canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to
`h`; that is, `h = φ ∘ πker`.  Moreover, `φ` is a *monomorphism* (injective homomorphism)
and is unique.

Our formal proof of this theorem will require function extensionality, proposition
extensionality, and a couple of truncation assumptions.  The extensionality
assumptions are postulated using `swelldef` and `pred-ext` which were defined
in [Base.Equality.Welldefined][] and [Base.Equality.Extensionality][]. As for
truncation, to prove that `φ` is injective we require

+   `buip`: *uniqueness of (block) identity proofs*; given two blocks of the kernel
    there is at most one proof that the blocks are equal;

To prove that `φ` is an embedding we require

+  `Bset`: *uniqueness of identity proofs* in the codomain; that is, the codomain
   `∣ 𝑩 ∣` is assumed to be a *set*.

Note that the classical, informal statement of the first homomorphism theorem does not
demand that `φ` be an embedding (in our sense of having subsingleton fibers), and if
we left this out of the consequent of our formal theorem statement, then we could omit
from the antecedent the assumption that `∣ 𝑩 ∣` is a set.

Without further ado, we present our formalization of the first homomorphism theorem.


```agda


open ≡-Reasoning

FirstHomTheorem|Set : (𝑨 : Algebra α)(𝑩 : Algebra β)(h : hom 𝑨 𝑩)
 {- extensionality assumptions -}  (pe : pred-ext α β)(fe : swelldef 𝓥 β)
 {- truncation assumptions -}      (Bset : is-set ∣ 𝑩 ∣)
                                   (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)
     -------------------------------------------------------------------------
 →   Σ[ φ ∈ hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩  ]
     ( ∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker fe{𝑩}h ∣ × IsInjective ∣ φ ∣  ×  is-embedding ∣ φ ∣  )

FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip = (φ , φhom) , ≡.refl , φmon , φemb
 where
  θ : Con 𝑨
  θ = kercon fe{𝑩} h
  ξ : IsEquivalence ∣ θ ∣
  ξ = IsCongruence.is-equivalence ∥ θ ∥

  φ : ∣ (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) ∣ → ∣ 𝑩 ∣
  φ a = ∣ h ∣ ⌞ a ⌟

  φhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 φ
  φhom 𝑓 a =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌞ a x ⌟) )  ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌞ a x ⌟)  ⟩
              (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌞ a x ⌟))  ≡⟨ ≡.cong (𝑓 ̂ 𝑩) ≡.refl     ⟩
              (𝑓 ̂ 𝑩) (λ x → φ (a x))            ∎

  φmon : IsInjective φ
  φmon {_ , mkblk u ≡.refl} {_ , mkblk v ≡.refl} φuv = block-ext|uip pe buip ξ φuv

  φemb : is-embedding φ
  φemb = monic-is-embedding|Set φ Bset φmon
```


Below we will prove that the homomorphism `φ`, whose existence we just proved, is
unique (see `NoetherHomUnique`), but first we show that if we add to the hypotheses
of the first homomorphism theorem the assumption that `h` is surjective, then we
obtain the so-called *first isomorphism theorem*.  Naturally, we let
`FirstHomTheorem|Set` do most of the work.


```agda


FirstIsoTheorem|Set : (𝑨 : Algebra α) (𝑩 : Algebra β) (h : hom 𝑨 𝑩)
 {- extensionality assumptions -}  (pe : pred-ext α β) (fe : swelldef 𝓥 β)
 {- truncation assumptions -}      (Bset : is-set ∣ 𝑩 ∣)
                                   (buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe{𝑩}h ∣)
 →                                 IsSurjective ∣ h ∣
 →                                 Σ[ f ∈ (epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)]
                                   ( ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
                                   × IsInjective ∣ f ∣ × is-embedding ∣ f ∣ )

FirstIsoTheorem|Set 𝑨 𝑩 h pe fe Bset buip hE =
 (fmap , fhom , fepic) , ≡.refl , (snd ∥ FHT ∥)
  where
  FHT = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip

  fmap : ∣ ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe ∣ → ∣ 𝑩 ∣
  fmap = fst ∣ FHT ∣

  fhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 fmap
  fhom = snd ∣ FHT ∣

  fepic : IsSurjective fmap
  fepic b = Goal where
   a : ∣ 𝑨 ∣
   a = SurjInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟪ a ⟫
   bfa = ((SurjInvIsInverseʳ ∣ h ∣ hE) b)⁻¹

   Goal : Image fmap ∋ b
   Goal = Image_∋_.eq ⟪ a ⟫ bfa
```


Now we prove that the homomorphism `φ`, whose existence is guaranteed by `FirstHomTheorem|Set`, is unique.


```agda


module _ {fe : swelldef 𝓥 β}(𝑨 : Algebra α)(𝑩 : Algebra β)(h : hom 𝑨 𝑩) where

 FirstHomUnique :  (f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 FirstHomUnique f g hfk hgk (_ , mkblk a ≡.refl) =
  ∣ f ∣ (_ , mkblk a ≡.refl)  ≡⟨ ≡.cong-app(hfk ⁻¹)a ⟩
  ∣ h ∣ a                     ≡⟨ ≡.cong-app(hgk)a ⟩
  ∣ g ∣ (_ , mkblk a ≡.refl)  ∎
```


If, in addition, we postulate extensionality of functions defined on the domain
`ker[ 𝑨 ⇒ 𝑩 ] h`, then we obtain the following variation of the last result.
(See [Base.Equality.Truncation][] for a discussion of *truncation*, *sets*,
and *uniqueness of identity proofs*.)

    fe-FirstHomUnique :  {fuww : funext (α ⊔ lsuc β) β}(f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
      →                  ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
      →                  ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
      →                  ∣ f ∣ ≡ ∣ g ∣

    fe-FirstHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.


```agda


 FirstIsoUnique :  (f g : epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 FirstIsoUnique f g hfk hgk = FirstHomUnique (epi→hom 𝑩 f) (epi→hom 𝑩 g) hfk hgk
```


--------------------------------------

<span style="float:left;">[← Base.Homomorphisms.Products](Base.Homomorphisms.Products.html)</span>
<span style="float:right;">[Base.Homomorphisms.Factor →](Base.Homomorphisms.Factor.html)</span>

{% include UALib.Links.md %}
