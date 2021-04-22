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

module Homomorphisms.Noether where

open import Homomorphisms.Basic public


module noether {𝑆 : Signature 𝓞 𝓥} where
 open homomorphisms {𝑆 = 𝑆} public

\end{code}


#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

Here we formalize a version of the *first homomorphism theorem*, sometimes called *Noether's first homomorphism theorem*, after Emmy Noether who was among the first proponents of the abstract approach to the subject that we now call "modern algebra").

Informally, the theorem states that every homomorphism from `𝑨` to `𝑩` (`𝑆`-algebras) factors through the quotient algebra `𝑨 ╱ ker h` (`𝑨` modulo the kernel of the given homomorphism).  In other terms, given `h : hom 𝑨 𝑩` there exists `φ : hom (𝑨 ╱ ker h) 𝑩` which, when composed with the canonical projection `πker : 𝑨 ↠ 𝑨 ╱ ker h`, is equal to `h`; that is, `h = φ ∘ πker`.  Moreover, `φ` is a *monomorphism* (injective homomorphism) and is unique.

Our formal proof of this theorem will require function extensionality as well as a couple of truncation assumptions. The function extensionality postulate (`fe`) will be clear enough.  As for truncation, proving that `φ` is monic will require the following postulates:<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

+ *Uniqueness of (codomain) Identity Proofs* (`UIPcod`): the codomain `∣ 𝑩 ∣` is a *set*, that is, has unique identity proofs.
+ *Uniqueness of (block) Membership Proofs* (`UMPblk`): given any pair of blocks of the kernel there is at most one proof that the given blocks are equal;

And proving that `φ` is an embedding requires

+ *Uniqueness of (kernel) Membership Proofs* (`UMPker`): the kernel of `h` inhabits the type `Pred₂` of *binary propositions* so there is at most one proof that a given pair belongs to the kernel relation;


Note that the classical, informal statement of the theorem does not demand that `φ` be an embedding (in our sense of having subsingleton fibers), and if we left this out of the consequent of the formal theorem statement below, then we could omit from the antecedent the assumption that ∣ 𝑩 ∣ is a set.

Without further ado, we present our formalization of the first homomorphism theorem.<sup>[2](Homomorphisms.Noether.html#fn2)</sup>

\begin{code}


 FirstHomTheorem|Set : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
                       -- extensionality assumptions:
                       (pe : pred-ext 𝓤 𝓦)(fe : dfunext 𝓥 𝓦)

                        -- truncation assumptions:
                        (Bset : is-set ∣ 𝑩 ∣)(buip : blk-uip ∣ 𝑨 ∣ ∣ kercon 𝑩 {fe} h ∣)

  → Σ φ ꞉ (hom (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩) , (∣ h ∣ ≡ ∣ φ ∣ ∘ ∣ πker 𝑩 {fe} h ∣) × Monic ∣ φ ∣ × is-embedding ∣ φ ∣

 FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip = (φ , φhom) , φcom , φmon , φemb
  where
   θ : Con 𝑨
   θ = kercon 𝑩 {fe} h
   ξ : IsEquivalence ∣ θ ∣
   ξ = IsCongruence.is-equivalence ∥ θ ∥

   φ : ∣ (𝑨 [ 𝑩 ]/ker h ↾ fe) ∣ → ∣ 𝑩 ∣
   φ a = ∣ h ∣ ⌞ a ⌟

   φhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩 φ
   φhom 𝑓 𝒂 =  ∣ h ∣ ( (𝑓 ̂ 𝑨) (λ x → ⌞ 𝒂 x ⌟) ) ≡⟨ ∥ h ∥ 𝑓 (λ x → ⌞ 𝒂 x ⌟)  ⟩
              (𝑓 ̂ 𝑩) (∣ h ∣ ∘ (λ x → ⌞ 𝒂 x ⌟)) ≡⟨ ap (𝑓 ̂ 𝑩) (fe λ x → refl) ⟩
              (𝑓 ̂ 𝑩) (λ x → φ (𝒂 x))             ∎

   φmon : Monic φ
   φmon (_ , (u , refl)) (_ , (v , refl)) φuv = block-ext|uip pe buip ξ φuv

   φcom : ∣ h ∣ ≡ φ ∘ ∣ πker 𝑩{fe} h ∣
   φcom = refl

   φemb : is-embedding φ
   φemb = monic-is-embedding|Set φ Bset φmon

\end{code}

Below we will prove that the homomorphism `φ`, whose existence we just proved, is unique (see `NoetherHomUnique`), but first we show that if we add to the hypotheses of the first homomorphism theorem the assumption that `h` is surjective, then we obtain the so-called *first isomorphism theorem*.  Naturally, we let `FirstHomTheorem|Set` do most of the work. (Note that the proof also requires an additional local function extensionality postulate.)

\begin{code}

 FirstIsoTheorem|Set : (𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩)
                       (pe : pred-ext 𝓤 𝓦)(fe : dfunext 𝓥 𝓦)(fww : dfunext 𝓦 𝓦)    -- extensionality assumptions
                       (Bset : is-set ∣ 𝑩 ∣)(buip :  blk-uip ∣ 𝑨 ∣ ∣ kercon 𝑩{fe}h ∣)  -- truncation assumptions:
  →   Epic ∣ h ∣
  →   Σ f ꞉ epi (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩 , (∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩{fe}h ∣) × Monic ∣ f ∣ × is-embedding ∣ f ∣

 FirstIsoTheorem|Set 𝑨 𝑩 h pe fe fww Bset buip hE = (fmap , fhom , fepic) , refl , (snd ∥ FHT ∥)
  where
  FHT = FirstHomTheorem|Set 𝑨 𝑩 h pe fe Bset buip  -- (φ , φhom) , φcom , φmon , φemb

  fmap : ∣ 𝑨 [ 𝑩 ]/ker h ↾ fe ∣ → ∣ 𝑩 ∣
  fmap = fst ∣ FHT ∣

  fhom : is-homomorphism (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩 fmap
  fhom = snd ∣ FHT ∣

  fepic : Epic fmap
  fepic b = γ where
   a : ∣ 𝑨 ∣
   a = EpicInv ∣ h ∣ hE b

   bfa : b ≡ fmap ⟪ a ⟫
   bfa = (cong-app (EpicInvIsRightInv {fe = fww} ∣ h ∣ hE) b)⁻¹

   γ : Image fmap ∋ b
   γ = Image_∋_.eq b ⟪ a ⟫ bfa

\end{code}

Now we prove that the homomorphism `φ`, whose existence is guaranteed by `FirstHomomorphismTheorem`, is unique.

\begin{code}

 module _ {fe : dfunext 𝓥 𝓦}(𝑨 : Algebra 𝓤 𝑆)(𝑩 : Algebra 𝓦 𝑆)(h : hom 𝑨 𝑩) where

  NoetherHomUnique : (f g : hom (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩)
   →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩 {fe} h ∣ → ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩{fe} h ∣
   →                 ∀ a  →  ∣ f ∣ a ≡ ∣ g ∣ a

  NoetherHomUnique f g hfk hgk (_ , (a , refl)) = ∣ f ∣ (_ , (a , refl)) ≡⟨ cong-app(hfk ⁻¹)a ⟩
                                                  ∣ h ∣ a                ≡⟨ cong-app(hgk)a ⟩
                                                  ∣ g ∣ (_ , (a , refl)) ∎

\end{code}

If, in addition, we postulate extensionality of functions defined on the domain `𝑨 [ 𝑩 ]/ker h`, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

  fe-NoetherHomUnique : {fuww : funext (𝓤 ⊔ lsuc 𝓦) 𝓦}(f g : hom (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩)
   →  ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩{fe} h ∣  →  ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩{fe} h ∣  →  ∣ f ∣ ≡ ∣ g ∣

  fe-NoetherHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

\end{code}

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.

\begin{code}

  NoetherIsoUnique : (f g : epi (𝑨 [ 𝑩 ]/ker h ↾ fe) 𝑩)
   →                 ∣ h ∣ ≡ ∣ f ∣ ∘ ∣ πker 𝑩{fe} h ∣ → ∣ h ∣ ≡ ∣ g ∣ ∘ ∣ πker 𝑩 {fe} h ∣
   →                 ∀ a → ∣ f ∣ a ≡ ∣ g ∣ a

  NoetherIsoUnique f g hfk hgk = NoetherHomUnique (epi-to-hom 𝑩 f) (epi-to-hom 𝑩 g) hfk hgk

\end{code}





#### <a id="homomorphism-composition">Homomorphism composition</a>

The composition of homomorphisms is again a homomorphism.  We formalize this in a number of alternative ways.

\begin{code}

 module _ (𝑨 : Algebra 𝓧 𝑆){𝑩 : Algebra 𝓨 𝑆}(𝑪 : Algebra 𝓩 𝑆) where

  ∘-hom : hom 𝑨 𝑩  →  hom 𝑩 𝑪  →  hom 𝑨 𝑪
  ∘-hom (g , ghom) (h , hhom) = h ∘ g , γ where

   γ : ∀ 𝑓 a → (h ∘ g)((𝑓 ̂ 𝑨) a) ≡ (𝑓 ̂ 𝑪)(h ∘ g ∘ a)

   γ 𝑓 a = (h ∘ g) ((𝑓 ̂ 𝑨) a) ≡⟨ ap h ( ghom 𝑓 a ) ⟩
           h ((𝑓 ̂ 𝑩) (g ∘ a)) ≡⟨ hhom 𝑓 ( g ∘ a ) ⟩
           (𝑓 ̂ 𝑪) (h ∘ g ∘ a) ∎


  ∘-is-hom : {f : ∣ 𝑨 ∣ → ∣ 𝑩 ∣} {g : ∣ 𝑩 ∣ → ∣ 𝑪 ∣}
   →         is-homomorphism 𝑨 𝑩 f → is-homomorphism 𝑩 𝑪 g
   →         is-homomorphism 𝑨 𝑪 (g ∘ f)

  ∘-is-hom {f} {g} fhom ghom = ∥ ∘-hom (f , fhom) (g , ghom) ∥

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
   →          kernel ∣ β ∣ ⊆ kernel ∣ α ∣ → Epic ∣ β ∣
              -------------------------------------------
   →          Σ φ ꞉ (hom 𝑪 𝑩) , ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣

  HomFactor fxy fzz 𝑩 α β Kβα βE = (φ , φIsHomCB) , αφβ
   where
   βInv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   βInv = λ y → (EpicInv ∣ β ∣ βE) y

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = λ y → ∣ α ∣ ( βInv y )

   ξ : (x : ∣ 𝑨 ∣) → kernel ∣ β ∣ (x , βInv (∣ β ∣ x))
   ξ x =  ( cong-app (EpicInvIsRightInv {fe = fzz} ∣ β ∣ βE) ( ∣ β ∣ x ) )⁻¹

   αφβ : ∣ α ∣ ≡ φ ∘ ∣ β ∣
   αφβ = fxy λ x → Kβα (ξ x)

   ι : (𝑓 : ∣ 𝑆 ∣)(𝒄 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑪 ∣) → 𝒄 ≡  ∣ β ∣ ∘ (βInv ∘ 𝒄)
   ι 𝑓 𝒄 = ap (λ - → - ∘ 𝒄) (EpicInvIsRightInv{fe = fzz} ∣ β ∣ βE)⁻¹

   useker : ∀ 𝑓 𝒄 → ∣ α ∣ (βInv (∣ β ∣((𝑓 ̂ 𝑨)(βInv ∘ 𝒄)))) ≡ ∣ α ∣((𝑓 ̂ 𝑨)(βInv ∘ 𝒄))
   useker 𝑓 𝒄 = Kβα (cong-app (EpicInvIsRightInv {fe = fzz} ∣ β ∣ βE)
                              (∣ β ∣ ((𝑓 ̂ 𝑨)(βInv ∘ 𝒄))))

   φIsHomCB : ∀ 𝑓 𝒄 → φ ((𝑓 ̂ 𝑪) 𝒄) ≡ ((𝑓 ̂ 𝑩)(φ ∘ 𝒄))

   φIsHomCB 𝑓 𝒄 = ∣ α ∣ (βInv ((𝑓 ̂ 𝑪) 𝒄))                   ≡⟨ i   ⟩
                 ∣ α ∣ (βInv ((𝑓 ̂ 𝑪)(∣ β ∣ ∘ (βInv ∘ 𝒄)))) ≡⟨ ii  ⟩
                 ∣ α ∣ (βInv (∣ β ∣ ((𝑓 ̂ 𝑨)(βInv ∘ 𝒄))))   ≡⟨ iii ⟩
                 ∣ α ∣ ((𝑓 ̂ 𝑨)(βInv ∘ 𝒄))                  ≡⟨ iv  ⟩
                 ((𝑓 ̂ 𝑩)(λ x → ∣ α ∣ (βInv (𝒄 x))))        ∎
    where
    i   = ap (∣ α ∣ ∘ βInv) (ap (𝑓 ̂ 𝑪) (ι 𝑓 𝒄))
    ii  = ap (∣ α ∣ ∘ βInv) (∥ β ∥ 𝑓 (βInv ∘ 𝒄))⁻¹
    iii = useker 𝑓 𝒄
    iv  = ∥ α ∥ 𝑓 (βInv ∘ 𝒄)

\end{code}

If, in addition to the hypotheses of the last theorem, we assume α is epic, then so is φ. (Note that the proof also requires an additional local function extensionality postulate, `funext 𝓨 𝓨`.)

\begin{code}

  HomFactorEpi : funext 𝓧 𝓨 → funext 𝓩 𝓩 → funext 𝓨 𝓨
   →             (𝑩 : Algebra 𝓨 𝑆)(α : hom 𝑨 𝑩)(β : hom 𝑨 𝑪)
   →             kernel ∣ β ∣ ⊆ kernel ∣ α ∣ → Epic ∣ β ∣ → Epic ∣ α ∣
                 ----------------------------------------------------------
   →             Σ φ ꞉ (epi 𝑪 𝑩) , ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣

  HomFactorEpi fxy fzz fyy 𝑩 α β kerincl βe αe = (fst ∣ φF ∣ , (snd ∣ φF ∣ , φE)) , ∥ φF ∥
   where
   φF : Σ φ ꞉ (hom 𝑪 𝑩) , ∣ α ∣ ≡ ∣ φ ∣ ∘ ∣ β ∣
   φF = HomFactor fxy fzz 𝑩 α β kerincl βe

   βinv : ∣ 𝑪 ∣ → ∣ 𝑨 ∣
   βinv = λ c → (EpicInv ∣ β ∣ βe) c

   αinv : ∣ 𝑩 ∣ → ∣ 𝑨 ∣
   αinv = λ b → (EpicInv ∣ α ∣ αe) b

   φ : ∣ 𝑪 ∣ → ∣ 𝑩 ∣
   φ = λ c → ∣ α ∣ ( βinv c )

   φE : Epic φ
   φE = epic-factor {fe = fyy} ∣ α ∣ ∣ β ∣ φ ∥ φF ∥ αe

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> See [Relations.Truncation][] for a discussion of *truncation*, *sets*, and *uniqueness of proofs*.</span>

<sup>2</sup><span class="footnote" id="fn2"> In this module we are already assuming *global* function extensionality (`gfe`), and we could just appeal to `gfe` (e.g., in the proof of `FirstHomomorphismTheorem`) instead of adding local function extensionality (\ab{fe}) to the list of assumptions.  However, we sometimes add an extra extensionality postulate in order to highlight where and how the principle is applied.}</span>

<br>
<br>

[← Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms →](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
