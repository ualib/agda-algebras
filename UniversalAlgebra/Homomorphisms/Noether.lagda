---
layout: default
title : Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}
-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Product using (_,_; Σ; _×_; Σ-syntax)
open import Function.Base  using (_∘_; id)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; cong-app)
open import Relation.Unary using (_⊆_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries using (Type; 𝓞; 𝓤; 𝓥; 𝓦; 𝓧; 𝓨; 𝓩; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; ∣_∣; ∥_∥; fst; snd; 𝑖𝑑)
open import Overture.Inverses using (IsInjective; IsSurjective; Image_∋_; SurjInv)
open import Relations.Discrete using (ker; kernel)
open import Relations.Quotients using (ker-IsEquivalence; _/_; ⟪_⟫; ⌞_⌟; R-block)
open import Relations.Truncation using (is-set; blk-uip; is-embedding; monic-is-embedding|Set)
open import Relations.Extensionality using (swelldef;  block-ext|uip; pred-ext; SurjInvIsRightInv; epic-factor)


module Homomorphisms.Noether {𝑆 : Signature 𝓞 𝓥} where

open import Algebras.Congruences{𝑆 = 𝑆} using (Con; IsCongruence)
open import Homomorphisms.Basic {𝑆 = 𝑆} using (hom; kercon; ker[_⇒_]_↾_; πker; is-homomorphism; epi; epi-to-hom)

\end{code}


#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

Here we formalize a version of the *first homomorphism theorem*, sometimes called *Noether's first homomorphism theorem*, after Emmy Noether who was among the first proponents of the abstract approach to the subject that we now call "modern algebra").

Informally, the theorem states that every homomorphism from `𝑨` to `𝑩` (`𝑆`-algebras) factors through the quotient algebra `𝑨 ╱ ker h` (`𝑨` modulo the kernel of the given homomorphism).  In other terms, given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩` which, when composed with the canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to `h`; that is, `h = φ ∘ πker`.  Moreover, `φ` is a *monomorphism* (injective homomorphism) and is unique.

Our formal proof of this theorem will require function extensionality, proposition extensionality, and a couple of truncation assumptions.  The extensionality assumptions are postulated using `dfunext` and `pred-ext` from [Overture.FunExtensionality][] and [Relations.Extensionality][] (resp.). As for truncation, to prove that `φ` is injective we require<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

+ `buip`: *uniqueness of (block) identity proofs*; given two blocks of the kernel there is at most one proof that the blocks are equal;

To prove that `φ` is an embedding we require

+ `Bset`: *uniqueness of identity proofs* in the codomain; that is, the codomain `∣ 𝑩 ∣` is assumed to be a *set*.

Note that the classical, informal statement of the first homomorphism theorem does not demand that `φ` be an embedding (in our sense of having subsingleton fibers), and if we left this out of the consequent of our formal theorem statement, then we could omit from the antecedent the assumption that `∣ 𝑩 ∣` is a set.

Without further ado, we present our formalization of the first homomorphism theorem.<sup>[2](Homomorphisms.Noether.html#fn2)</sup>

\begin{code}


FirstHomTheorem|Set :

    (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
    (pe : pred-ext 𝓤 𝓦)(fe : swelldef 𝓥 𝓦)                              -- extensionality assumptions
    (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣)     -- truncation assumptions
    -----------------------------------------------------------------------------------------------------------
 →  Σ[ φ ꞉ hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩  ] ((∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker fe{𝑩}h ∣) × IsInjective ∣ φ ∣ × is-embedding ∣ φ ∣)

FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip = (φ , φhom) , refl , φmon , φemb
 where
  θ : Con 𝑨
  θ = kercon fe{𝑩} h
  ξ : IsEquivalence ∣ θ ∣
  ξ = IsCongruence.is-equivalence ∥ θ ∥

  φ : ∣ (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) ∣ → ∣ 𝑩 ∣
  φ a = ∣ h ∣ ⌞ a ⌟

  φhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 φ
  φhom 𝑓 a = ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌞ a x ⌟) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌞ a x ⌟)  ⟩
             (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌞ a x ⌟))  ≡⟨ cong (𝑓 ̂ 𝑩) refl ⟩
             (𝑓 ̂ 𝑩) (λ x → φ (a x))            ∎

  φmon : IsInjective φ
  φmon {_ , R-block u refl} {_ , R-block v refl} φuv = block-ext|uip pe buip ξ φuv

  φemb : is-embedding φ
  φemb = monic-is-embedding|Set φ Bset φmon

\end{code}

Below we will prove that the homomorphism `φ`, whose existence we just proved, is unique (see `NoetherHomUnique`), but first we show that if we add to the hypotheses of the first homomorphism theorem the assumption that `h` is surjective, then we obtain the so-called *first isomorphism theorem*.  Naturally, we let `FirstHomTheorem|Set` do most of the work. (Note that the proof also requires an additional local function extensionality postulate.)

\begin{code}

FirstIsoTheorem|Set :

     (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
     (pe : pred-ext 𝓤 𝓦)(fe : swelldef 𝓥 𝓦)(fww : funext 𝓦 𝓦)       -- extensionality assumptions
     (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe{𝑩}h ∣)  -- truncation assumptions
 →   IsSurjective ∣ h ∣
     -----------------------------------------------------------------------------------------------------------
 →   Σ[ f ∈ (epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)] (∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣) × IsInjective ∣ f ∣ × is-embedding ∣ f ∣

FirstIsoTheorem|Set 𝑨 𝑩 h pe fe fww Bset buip hE = (fmap , fhom , fepic) , refl , (snd ∥ FHT ∥)
 where
  FHT = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip

  fmap : ∣ ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe ∣ → ∣ 𝑩 ∣
  fmap = fst ∣ FHT ∣

  fhom : is-homomorphism (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩 fmap
  fhom = snd ∣ FHT ∣

  fepic : IsSurjective fmap
  fepic b = γ where
   a : ∣ 𝑨 ∣
   a = SurjInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟪ a ⟫
   bfa = (cong-app (SurjInvIsRightInv {fe = fww} ∣ h ∣ hE) b)⁻¹

   γ : Image fmap ∋ b
   γ = Image_∋_.eq b ⟪ a ⟫ bfa

\end{code}

Now we prove that the homomorphism `φ`, whose existence is guaranteed by `FirstHomTheorem|Set`, is unique.

\begin{code}

module _ {fe : swelldef 𝓥 𝓦}(𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) where

 NoetherHomUnique : (f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣ → ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherHomUnique f g hfk hgk (_ , R-block a refl) = ∣ f ∣ (_ , R-block a refl) ≡⟨ cong-app(hfk ⁻¹)a ⟩
                                                     ∣ h ∣ a                    ≡⟨ cong-app(hgk)a ⟩
                                                     ∣ g ∣ (_ , R-block a refl) ∎

\end{code}

If, in addition, we postulate extensionality of functions defined on the domain `ker[ 𝑨 ⇒ 𝑩 ] h`, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 fe-NoetherHomUnique : {fuww : funext (𝓤 ⊔ lsuc 𝓦) 𝓦}(f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →  ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣  →  ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣  →  ∣ f ∣ ≡ ∣ g ∣

 fe-NoetherHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

\end{code}

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.

\begin{code}

 NoetherIsoUnique : (f g : epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣ → ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherIsoUnique f g hfk hgk = NoetherHomUnique (epi-to-hom 𝑩 f) (epi-to-hom 𝑩 g) hfk hgk

\end{code}







#### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

If `α : hom 𝑨 𝑩`, `β : hom 𝑨 𝑪`, `β` is surjective, and `ker β ⊆ ker α`, then there exists `φ : hom 𝑪 𝑩` such that `α = φ ∘ β` so the following diagram commutes:

```
𝑨 --- β ->> 𝑪
 \         .
  \       .
   α     φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {𝑨 : Algebra 𝓧 𝑆}{𝑪 : Algebra 𝓩 𝑆} where

 HomFactor : funext 𝓧 𝓨 → funext 𝓩 𝓩 → (𝑩 : Algebra 𝓨 𝑆)(α : hom 𝑨 𝑩)(β : hom 𝑨 𝑪)
  →          kernel ∣ β ∣ ⊆ kernel ∣ α ∣ → IsSurjective ∣ β ∣
             -------------------------------------------
  →          Σ[ φ ∈ (hom 𝑪 𝑩)] ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣

 HomFactor fxy fzz 𝑩 α β Kβα βE = (φ , φIsHomCB) , αφβ
  where
   βInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   βInv = SurjInv ∣ β ∣ βE

   η : ∣ β ∣ ∘ βInv ≡ 𝑖𝑑 ∣ 𝑪 ∣
   η = SurjInvIsRightInv{fe = fzz} ∣ β ∣ βE

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ α ∣ ∘ βInv

   ξ : ∀ a → kernel ∣ β ∣ (a , βInv (∣ β ∣ a))
   ξ a = (cong-app η (∣ β ∣ a))⁻¹

   αφβ : ∣ α ∣ ≡ φ ∘ ∣ β ∣
   αφβ = fxy λ x → Kβα (ξ x)

   φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
   φIsHomCB 𝑓 c = φ ((𝑓 ̂ 𝑪) c)                    ≡⟨ cong(φ ∘(𝑓 ̂ 𝑪))(cong (λ - → - ∘ c)η ⁻¹)⟩
                  φ ((𝑓 ̂ 𝑪)(∣ β ∣ ∘(βInv ∘ c)))   ≡⟨ cong φ (∥ β ∥ 𝑓 (βInv ∘ c))⁻¹ ⟩
                  φ (∣ β ∣((𝑓 ̂ 𝑨)(βInv ∘ c)))     ≡⟨ cong-app(αφβ ⁻¹)((𝑓 ̂ 𝑨)(βInv ∘ c))⟩
                  ∣ α ∣((𝑓 ̂ 𝑨)(βInv ∘ c))         ≡⟨ ∥ α ∥ 𝑓 (βInv ∘ c) ⟩
                  (𝑓 ̂ 𝑩)(λ x → ∣ α ∣(βInv (c x))) ∎

\end{code}

If, in addition to the hypotheses of the last theorem, we assume α is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext 𝓨 𝓨`.)

\begin{code}

 HomFactorEpi : funext 𝓧 𝓨 → funext 𝓩 𝓩 → funext 𝓨 𝓨
  →             (𝑩 : Algebra 𝓨 𝑆)(α : hom 𝑨 𝑩)(β : hom 𝑨 𝑪)
  →             kernel ∣ β ∣ ⊆ kernel ∣ α ∣ → IsSurjective ∣ β ∣ → IsSurjective ∣ α ∣
                ----------------------------------------------------------
  →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣

 HomFactorEpi fxy fzz fyy 𝑩 α β kerincl βe αe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣
   φF = HomFactor fxy fzz 𝑩 α β kerincl βe

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ α ∣ ∘ (SurjInv ∣ β ∣ βe)

   φE : IsSurjective φ
   φE = epic-factor {fe = fyy} ∣ α ∣ ∣ β ∣ φ ∥ φF ∥ αe

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> See [Relations.Truncation][] for a discussion of *truncation*, *sets*, and *uniqueness of identity proofs*.</span>

<sup>2</sup><span class="footnote" id="fn2"> In this module we are already assuming *global* function extensionality (`gfe`), and we could just appeal to `gfe` (e.g., in the proof of `FirstHomomorphismTheorem`) instead of adding local function extensionality (\ab{fe}) to the list of assumptions.  However, we sometimes add an extra extensionality postulate in order to highlight where and how the principle is applied.}</span>

<br>
<br>

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
