---
layout: default
title : Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-01-13
author: [the ualib/agda-algebras development team][]
---

### <a id="homomorphism-theorems">Homomorphism Theorems</a>

This chapter presents the [Homomorphisms.Noether][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level using ( Level ; Lift )
open import Algebras.Basic

module Homomorphisms.Noether {𝓞 𝓥 : Level} (𝑆 : Signature 𝓞 𝓥) where


-- Imports from Agda (builtin/primitive) and the Agda Standard Library ---------------------
open import Axiom.Extensionality.Propositional    using    ()
                                                  renaming (Extensionality to funext)
open import Agda.Primitive                        using    ( _⊔_      ;   lsuc  )
                                                  renaming ( Set      to  Type  )
open import Agda.Builtin.Equality                 using    ( _≡_      ;   refl  )
open import Data.Product                          using    ( _,_      ;   Σ
                                                           ; Σ-syntax ;   _×_   )
                                                  renaming ( proj₁    to  fst
                                                           ; proj₂    to  snd   )
open import Function.Base                         using    ( _∘_      ;   id    )
open import Relation.Binary                       using    ( IsEquivalence   )
open import Relation.Binary.PropositionalEquality using    ( trans    ;   cong
                                                           ; cong-app
                                                           ; module ≡-Reasoning )
open import Relation.Unary                        using    ( _⊆_ )


-- Imports from agda-algebras --------------------------------------------------------------
open import Overture.Preliminaries   using ( ∣_∣ ; ∥_∥ ; 𝑖𝑑 ; _⁻¹ )
open import Overture.Inverses        using ( IsInjective ; IsSurjective ; Image_∋_ ; SurjInv )
open import Relations.Discrete       using ( ker ; kernel )
open import Relations.Quotients      using ( ker-IsEquivalence ; _/_ ; ⟪_⟫ ; ⌞_⌟ ; R-block)
open import Relations.Truncation     using ( is-set ; blk-uip ; is-embedding
                                           ; monic-is-embedding|Set )
open import Relations.Extensionality using ( swelldef ; block-ext|uip ; pred-ext
                                           ; SurjInvIsRightInv ; epic-factor )
open import Algebras.Congruences   𝑆 using ( Con ; IsCongruence )
open import Homomorphisms.Basic    𝑆 using ( hom ; kercon ; ker[_⇒_]_↾_ ; πker
                                           ; is-homomorphism ; epi ; epi-to-hom )

private variable α β γ : Level

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
open ≡-Reasoning

FirstHomTheorem|Set :

    (𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩)
    (pe : pred-ext α β)(fe : swelldef 𝓥 β)                          -- extensionality assumptions
    (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe {𝑩} h ∣) -- truncation assumptions
    ----------------------------------------------------------------
 →  Σ[ φ ∈ hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩  ]
                            ( ( ∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker fe{𝑩}h ∣ )
                              × IsInjective ∣ φ ∣  ×  is-embedding ∣ φ ∣  )

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

     (𝑨 : Algebra α 𝑆) (𝑩 : Algebra β 𝑆) (h : hom 𝑨 𝑩)
     (pe : pred-ext α β) (fe : swelldef 𝓥 β)                        -- extensionality assumptions
     (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon fe{𝑩}h ∣)  -- truncation assumptions
 →   IsSurjective ∣ h ∣
     ---------------------------------------------------------------
 →   Σ[ f ∈ (epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)]
                          ( ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣ )
                            × IsInjective ∣ f ∣ × is-embedding ∣ f ∣

FirstIsoTheorem|Set 𝑨 𝑩 h pe fe Bset buip hE =
 (fmap , fhom , fepic) , refl , (snd ∥ FHT ∥)
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
   bfa = ((SurjInvIsRightInv ∣ h ∣ hE) b)⁻¹

   Goal : Image fmap ∋ b
   Goal = Image_∋_.eq ⟪ a ⟫ bfa

\end{code}

Now we prove that the homomorphism `φ`, whose existence is guaranteed by `FirstHomTheorem|Set`, is unique.

\begin{code}

module _ {fe : swelldef 𝓥 β}(𝑨 : Algebra α 𝑆)(𝑩 : Algebra β 𝑆)(h : hom 𝑨 𝑩) where

 NoetherHomUnique : (f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherHomUnique f g hfk hgk (_ , R-block a refl) =
  ∣ f ∣ (_ , R-block a refl) ≡⟨ cong-app(hfk ⁻¹)a ⟩
  ∣ h ∣ a                    ≡⟨ cong-app(hgk)a ⟩
  ∣ g ∣ (_ , R-block a refl) ∎

\end{code}

If, in addition, we postulate extensionality of functions defined on the domain `ker[ 𝑨 ⇒ 𝑩 ] h`, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 fe-NoetherHomUnique : {fuww : funext (α ⊔ lsuc β) β}(f g : hom (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                    ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                    ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                    ∣ f ∣ ≡ ∣ g ∣

 fe-NoetherHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

\end{code}

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.

\begin{code}

 NoetherIsoUnique : (f g : epi (ker[ 𝑨 ⇒ 𝑩 ] h ↾ fe) 𝑩)
  →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker fe{𝑩}h ∣
  →                 ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

 NoetherIsoUnique f g hfk hgk = NoetherHomUnique (epi-to-hom 𝑩 f) (epi-to-hom 𝑩 g) hfk hgk

\end{code}







#### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

If `τ : hom 𝑨 𝑩`, `ν : hom 𝑨 𝑪`, `ν` is surjective, and `ker ν ⊆ ker τ`, then there exists `φ : hom 𝑪 𝑩` such that `τ = φ ∘ ν` so the following diagram commutes:

```
𝑨 --- ν ->> 𝑪
 \         .
  \       .
   τ     φ
    \   .
     \ .
      V
      𝑩
```

\begin{code}

module _ {𝑨 : Algebra α 𝑆}{𝑪 : Algebra γ 𝑆} where

 HomFactor : funext α β → swelldef 𝓥 γ
  →          (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →          kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣ → IsSurjective ∣ ν ∣
             --------------------------------------------------
  →          Σ[ φ ∈ (hom 𝑪 𝑩)] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣

 HomFactor fxy wd 𝑩 τ ν Kντ νE = (φ , φIsHomCB) , τφν
  where
   νInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   νInv = SurjInv ∣ ν ∣ νE

   η : ∀ c → ∣ ν ∣ (νInv c) ≡ c
   η c = SurjInvIsRightInv ∣ ν ∣ νE c

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ νInv

   ξ : ∀ a → kernel ∣ ν ∣ (a , νInv (∣ ν ∣ a))
   ξ a = (η (∣ ν ∣ a))⁻¹

   τφν : ∣ τ ∣ ≡ φ ∘ ∣ ν ∣
   τφν = fxy λ x → Kντ (ξ x)

   φIsHomCB : ∀ 𝑓 c → φ ((𝑓 ̂ 𝑪) c) ≡ ((𝑓 ̂ 𝑩)(φ ∘ c))
   φIsHomCB 𝑓 c = φ ((𝑓 ̂ 𝑪) c)     ≡⟨ cong φ (wd (𝑓 ̂ 𝑪) c (∣ ν ∣ ∘ (νInv ∘ c)) (λ i → (η (c i))⁻¹)) ⟩
                  φ ((𝑓 ̂ 𝑪)(∣ ν ∣ ∘(νInv ∘ c)))   ≡⟨ cong φ (∥ ν ∥ 𝑓 (νInv ∘ c))⁻¹ ⟩
                  φ (∣ ν ∣((𝑓 ̂ 𝑨)(νInv ∘ c)))     ≡⟨ cong-app(τφν ⁻¹)((𝑓 ̂ 𝑨)(νInv ∘ c))⟩
                  ∣ τ ∣((𝑓 ̂ 𝑨)(νInv ∘ c))         ≡⟨ ∥ τ ∥ 𝑓 (νInv ∘ c) ⟩
                  (𝑓 ̂ 𝑩)(λ x → ∣ τ ∣(νInv (c x))) ∎

\end{code}

If, in addition to the hypotheses of the last theorem, we assume τ is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext β β`.)

\begin{code}

 HomFactorEpi : funext α β → swelldef 𝓥 γ
  →             (𝑩 : Algebra β 𝑆)(τ : hom 𝑨 𝑩)(ν : hom 𝑨 𝑪)
  →             kernel ∣ ν ∣ ⊆ kernel ∣ τ ∣
  →             IsSurjective ∣ ν ∣ → IsSurjective ∣ τ ∣
                ---------------------------------------------
  →             Σ[ φ ∈ epi 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣

 HomFactorEpi fxy wd 𝑩 τ ν kerincl νe τe = (fst ∣ φF ∣ ,(snd ∣ φF ∣ , φE)), ∥ φF ∥
  where
   φF : Σ[ φ ∈ hom 𝑪 𝑩 ] ∣ τ ∣ ≡ ∣ φ ∣ ∘ ∣ ν ∣
   φF = HomFactor fxy wd 𝑩 τ ν kerincl νe

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = ∣ τ ∣ ∘ (SurjInv ∣ ν ∣ νe)

   φE : IsSurjective φ
   φE = epic-factor  ∣ τ ∣ ∣ ν ∣ φ ∥ φF ∥ τe

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> See [Relations.Truncation][] for a discussion of *truncation*, *sets*, and *uniqueness of identity proofs*.</span>

<sup>2</sup><span class="footnote" id="fn2"> In this module we are already assuming *global* function extensionality (`gfe`), and we could just appeal to `gfe` (e.g., in the proof of `FirstHomomorphismTheorem`) instead of adding local function extensionality (\ab{fe}) to the list of assumptions.  However, we sometimes add an extra extensionality postulate in order to highlight where and how the principle is applied.}</span>

<br>
<br>

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}


------------------------------

[the ualib/agda-algebras development team]: https://github.com/ualib/agda-algebras#the-ualib-agda-algebras-development-team
