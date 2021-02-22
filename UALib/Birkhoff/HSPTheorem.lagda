---
layout: default
title : UALib.Birkhoff.HSPTheorem (The Agda Universal Algebra Library)
date : 2021-02-02
author: William DeMeo
---

### <a id="hsp-theorem">HSP Theorem</a>

This section presents the [UALib.Birkhoff.HSPTheorem][] module of the [Agda Universal Algebra Library][].<sup>1</sup>

To complete the proof of Birkhoff's HSP theorem, it remains to show that every algebra 𝑨 that belongs to `Mod X (Th (V 𝒦))`---i.e., every algebra that models the equations in Th (V 𝒦)---belongs to V 𝒦.  This will prove that V 𝒦 is an equational class.  The converse, that every equational class is a variety was already proved; see the remarks at the end of this module.

We accomplish our goal by constructing an algebra 𝔽 with the following properties:

1. 𝔽 ∈ V 𝒦 and

2. Every 𝑨 ∈ Mod X (Th (V 𝒦)) is a homomorphic image of 𝔽.

In earlier versions of the [Agda UALib][], the free algebra 𝔉 developed in the [Birkhoff.FreeAlgebra][] section played the role of the algebra 𝔽 with properties 1 and 2.  However, we found a more direct path to the proof using the algebra `𝔽 := (𝑻 X) [ ℭ ]/ker ΨTC`, where ℭ is the product of all subalgebras of algebras in 𝒦 and ΨTC is the homomorphism from 𝑻 X to ℭ defined by ΨTC := ⨅-hom-co gfe (𝑻 X) {ℑs}{𝔄s}(λ i → (T𝔄 i)).

Recall, `⨅-hom-co` (defined in [Homomorphisms.Basic](UALib.Homomorphisms.Basic.html#product-homomorphisms)) takes an 𝑆-algebra 𝑨, a family {ℬ : I → Algebra 𝓤 𝑆} of 𝑆-algebras, and a family `ℋ : ∀ i → hom 𝑨 (ℬ i)` of homomorphisms and constructs the natural homomorphism ϕ from 𝑨 to the product ⨅ ℬ.  The homomorphism ϕ : hom 𝑨 (⨅ ℬ) is natural in the sense that the i-th component of the image of 𝑎 : ∣ 𝑨 ∣ under ϕ is the image ∣ ℋ i ∣ 𝑎 of 𝑎 under the i-th homomorphism ℋ i.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇; _⊔_; _⁺; propext; hfunext)
open import UALib.Relations.Unary using (Pred)

\end{code}

Unlike previous modules, in this module we fix 𝓤, X, and 𝒦 in advance.

\begin{code}

module UALib.Birkhoff.HSPTheorem
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {𝓤 : Universe} {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 -- extensionality assumptions:
    {pe : propext 𝓤}
    {pe' : propext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
    {hfe : hfunext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where

open import UALib.Birkhoff.FreeAlgebra {𝑆 = 𝑆}{gfe} hiding (Pred; _⊔_; _⁺; propext; hfunext; Algebra; _̇ ) public
open the-free-algebra {𝓤}{𝓤}{X}

\end{code}


#### <a id="F-in-classproduct">𝔽 ≤  ⨅ S(𝒦)</a>
Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial. We must prove that the free algebra embeds in the product ℭ of all subalgebras of algebras in the class 𝒦.  This is really the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that ℭ be a set.

We begin by constructing ℭ, using the class-product types described in the section on <a href="https://ualib.gitlab.io/UALib.Varieties.Varieties.html#products-of-classes">products of classes</a>.

\begin{code}

open the-relatively-free-algebra {𝓤 = 𝓤}{𝓧 = 𝓤}{X = X} {𝒦 = 𝒦}

-- NOTATION.
ℑs : 𝓸𝓿𝓾 ̇
ℑs = ℑ{𝓤}{𝓤}{X} (S{𝓤}{𝓤} 𝒦)
𝔄s : ℑs → Algebra 𝓤 𝑆
𝔄s = λ (i : ℑs) → ∣ i ∣

SK𝔄 : (i : ℑs) → (𝔄s i) ∈ S{𝓤}{𝓤} 𝒦
SK𝔄 = λ (i : ℑs) → fst ∥ i ∥

𝔄h : (i : ℑs) → X → ∣ 𝔄s i ∣
𝔄h = λ (i : ℑs) → snd ∥ i ∥

-- ℭ is the product of all subalgebras of algebras in 𝒦.
ℭ : Algebra 𝓸𝓿𝓾 𝑆
ℭ = ⨅ 𝔄s

\end{code}

Observe that the inhabitants of ℭ are maps from ℑs to {𝔄s i : i ∈ ℑs}.

\begin{code}

T𝔄 : ∀ i → hom (𝑻 X) (𝔄s i)
T𝔄 i = lift-hom (𝔄s i) (𝔄h i)

ΨTC : hom (𝑻 X) ℭ
ΨTC = ⨅-hom-co gfe (𝑻 X) {ℑs}{𝔄s}(λ i → (T𝔄 i))

\end{code}


#### <a id="the-new-free-algebra">The new free algebra</a>

As mentioned above, the initial version of the [Agda UALib][] used the free algebra 𝔉, developed in the [Birkhoff.FreeAlgebra][] module.  However, our new, more direct proof uses the algebra 𝔽, which we now define.

\begin{code}

𝔽 : Algebra 𝓸𝓿𝓾+ 𝑆
𝔽 = (𝑻 X) [ ℭ ]/ker ΨTC

\end{code}

It might be an instructive exercise to prove that 𝔽 is, in fact, isomorphic to the free algebra 𝔉 that we defined in the [UALib.Birkhoff.FreeAlgebra][] module.

\begin{code}

Ψe : epi (𝑻 X) 𝔽
Ψe = πker ℭ ΨTC

Ψ : hom (𝑻 X) 𝔽
Ψ = epi-to-hom 𝔽 Ψe

ΨE : Epic ∣ Ψ ∣
ΨE = snd ∥ Ψe ∥

\end{code}

We will need the following facts relating ΨTC, Ψ, and ψ.

\begin{code}

ψlemma0 : ∀ p q → (∣ ΨTC ∣ p ≡ ∣ ΨTC ∣ q) → (p , q) ∈ ψ 𝒦
ψlemma0 p q pΨTCq 𝑨 sA h = ap (λ - → - (𝑨 , (sA , h))) pΨTCq


ψlemma0-ap : {𝑨 : Algebra 𝓤 𝑆}{h : X → ∣ 𝑨 ∣}
 →           𝑨 ∈ S{𝓤}{𝓤} 𝒦
             ---------------------------------------
 →           KER-pred ∣ Ψ ∣ ⊆ KER-pred (free-lift 𝑨 h)

ψlemma0-ap {𝑨}{h} skA {p , q} x = γ where

  ν : ∣ ΨTC ∣ p ≡ ∣ ΨTC ∣ q
  ν = ker-in-con (𝑻 X) (kercon ℭ ΨTC) p q x

  γ : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
  γ = ((ψlemma0 p q) ν) 𝑨 skA h


\end{code}

We now use `ψlemma0-ap` to prove that, for every subalgebra `𝑨` of an algebra in `𝒦`, every map from `X` to `∣ 𝑨 ∣` lifts to a homomorphism from `𝔽` to `𝑨`.

\begin{code}

𝔽-lift-hom : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
𝔽-lift-hom 𝑨 skA h = fst(HomFactor (𝑻 X){𝑨}{𝔽}(lift-hom 𝑨 h) Ψ ΨE (ψlemma0-ap skA))

\end{code}


#### <a id="k-models-psi">𝒦 models ψ</a>

The goal of this subsection is to prove that `𝒦` models `ψ 𝒦`. In other terms, for all pairs `(p , q) ∈ Term X × Term X` of terms, if `(p , q) ∈ ψ 𝒦`, then `𝒦 ⊧ p ≋ q`.

\begin{code}

X↪𝔽 : X → ∣ 𝔽 ∣
X↪𝔽 x = ⟦ ℊ x ⟧

𝔛 : hom (𝑻 X) 𝔽
𝔛 = lift-hom 𝔽 X↪𝔽

Ψ-is-lift-hom : ∀ p → ∣ 𝔛 ∣ p ≡ ∣ Ψ ∣ p
Ψ-is-lift-hom (ℊ x) = 𝓇ℯ𝒻𝓁
Ψ-is-lift-hom (node 𝑓 𝒕) = ∣ 𝔛 ∣ (node 𝑓 𝒕)           ≡⟨ ∥ 𝔛 ∥ 𝑓 𝒕 ⟩
                          (𝑓 ̂ 𝔽)(λ i → ∣ 𝔛 ∣(𝒕 i))  ≡⟨ ap(𝑓 ̂ 𝔽)(gfe (λ x → Ψ-is-lift-hom(𝒕 x))) ⟩
                          (𝑓 ̂ 𝔽)(λ i → ∣ Ψ ∣ (𝒕 i))  ≡⟨ (∥ Ψ ∥ 𝑓 𝒕)⁻¹ ⟩
                          ∣ Ψ ∣ (node 𝑓 𝒕)           ∎


ψlemma1 : KER-pred ∣ 𝔛 ∣ ⊆ ψ 𝒦
ψlemma1 {p , q} 𝔛pq 𝑨 sA h = γ
 where
  f : hom 𝔽 𝑨
  f = 𝔽-lift-hom 𝑨 sA h

  h' ϕ : hom (𝑻 X) 𝑨
  h' = HomComp (𝑻 X) 𝑨 𝔛 f
  ϕ = lift-hom 𝑨 h

  f𝔛≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ 𝔛 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
  f𝔛≡ϕ x = 𝓇ℯ𝒻𝓁
  h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ 𝔛 ∣) t ≡ ∣ ϕ ∣ t
  h≡ϕ t = free-unique gfe 𝑨 h' ϕ f𝔛≡ϕ t

  γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
  γ = ∣ ϕ ∣ p         ≡⟨ (h≡ϕ p)⁻¹ ⟩
      ∣ f ∣ ( ∣ 𝔛 ∣ p ) ≡⟨ ap ∣ f ∣ 𝔛pq ⟩
      ∣ f ∣ ( ∣ 𝔛 ∣ q ) ≡⟨ h≡ϕ q ⟩
      ∣ ϕ ∣ q ∎


ψlemma2 : KER-pred ∣ Ψ ∣ ⊆ ψ 𝒦
ψlemma2 {p , q} hyp = ψlemma1 {p , q} γ
  where
   γ : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
   γ = (Ψ-is-lift-hom p) ∙ hyp ∙ (Ψ-is-lift-hom q)⁻¹


ψlemma3 : ∀ p q → (p , q) ∈ ψ 𝒦 → 𝒦 ⊧ p ≋ q
ψlemma3 p q pψq {𝑨} kA = γ
 where
  skA : 𝑨 ∈ S 𝒦
  skA = siso (sbase kA) (sym-≅ lift-alg-≅)

  γ : (p ̇ 𝑨) ≡ (q ̇ 𝑨)
  γ = gfe λ h → (p ̇ 𝑨) h         ≡⟨ free-lift-interp 𝑨 h p ⟩
                (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 skA h ⟩
                (free-lift 𝑨 h) q ≡⟨ (free-lift-interp 𝑨 h q)⁻¹  ⟩
                (q ̇ 𝑨) h         ∎


class-models-kernel : ∀ p q → (p , q) ∈ KER-pred ∣ Ψ ∣ → 𝒦 ⊧ p ≋ q
class-models-kernel  p q hyp = ψlemma3 p q (ψlemma2 hyp)


kernel-in-theory : KER-pred ∣ Ψ ∣ ⊆ Th (V 𝒦)
kernel-in-theory {p , q} pKq = (class-ids-⇒ p q (class-models-kernel p q pKq))


\end{code}

Finally we come to one of the main theorems of this module; it asserts that every algebra in `Mod X (Th 𝕍𝒦)` is a homomorphic image of 𝔽.  We prove this below as the function (or proof object) `𝔽-ModTh-epi`.

\begin{code}

open Congruence
free-quot-subalg-ℭ : is-set ∣ ℭ ∣
 →                   (∀ p q → is-subsingleton (⟨ kercon ℭ ΨTC ⟩ p q))
 →                   (∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon ℭ ΨTC ⟩} C))
                     -----------------------------------------------------------
 →                   ((𝑻 X) [ ℭ ]/ker ΨTC) ≤ ℭ

free-quot-subalg-ℭ Cset ssR ssC = FirstHomCorollary (𝑻 X) ℭ ΨTC pe' Cset ssR ssC


module _ (Cset : is-set ∣ ℭ ∣)
         (ssR : ∀ p q → is-subsingleton (⟨ kercon ℭ ΨTC ⟩ p q))
         (ssC : ∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon ℭ ΨTC ⟩} C)) where

 𝔽≤ℭ : ((𝑻 X) [ ℭ ]/ker ΨTC) ≤ ℭ
 𝔽≤ℭ = free-quot-subalg-ℭ Cset ssR ssC

 𝕍𝒦 : Pred (Algebra 𝓸𝓿𝓾+ 𝑆) 𝓸𝓿𝓾++
 𝕍𝒦 = V{𝓤}{𝓸𝓿𝓾+} 𝒦

 𝔽-ModTh-epi : (𝑨 : Algebra 𝓸𝓿𝓾+ 𝑆) → 𝑨 ∈ Mod X (Th 𝕍𝒦) → epi 𝔽 𝑨
 𝔽-ModTh-epi 𝑨 AinMTV = γ
  where
   ϕ : hom (𝑻 X) 𝑨
   ϕ = lift-hom 𝑨 (fst(𝕏 𝑨))

   ϕE : Epic ∣ ϕ ∣
   ϕE = lift-of-epi-is-epi 𝑨 (fst (𝕏 𝑨)) (snd (𝕏 𝑨))

   pqlem2 : ∀ p q → (p , q) ∈ KER-pred ∣ Ψ ∣ → 𝑨 ⊧ p ≈ q
   pqlem2 p q hyp = AinMTV p q (kernel-in-theory hyp)

   kerincl : KER-pred ∣ Ψ ∣ ⊆ KER-pred ∣ ϕ ∣
   kerincl {p , q} x = γ
    where
     Apq : 𝑨 ⊧ p ≈ q
     Apq = pqlem2 p q x
     γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
     γ = ∣ ϕ ∣ p                    ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         free-lift 𝑨 (fst(𝕏 𝑨)) p ≡⟨ (free-lift-interp 𝑨 (fst(𝕏 𝑨)) p)⁻¹ ⟩
         (p ̇ 𝑨) (fst(𝕏 𝑨))       ≡⟨ intens (pqlem2 p q x) (fst(𝕏 𝑨))  ⟩
         (q ̇ 𝑨) (fst(𝕏 𝑨))       ≡⟨ free-lift-interp 𝑨 (fst(𝕏 𝑨)) q ⟩
         free-lift 𝑨 (fst(𝕏 𝑨)) q ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
         ∣ ϕ ∣ q                  ∎

   γ : epi 𝔽 𝑨
   γ = fst (HomFactorEpi (𝑻 X){𝑨}{𝔽} ϕ ϕE Ψ ΨE  kerincl)


\end{code}

#### <a id="F-in-VK">𝔽 ∈ V(𝒦)</a>

With this result in hand, along with what we proved earlier---namely, PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦---it is not hard to show that 𝔽 belongs to V 𝒦.

\begin{code}

 𝔽∈SP : 𝔽 ∈ (S{𝓸𝓿𝓾}{𝓸𝓿𝓾+} (P{𝓤}{𝓸𝓿𝓾} 𝒦))
 𝔽∈SP = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

 𝔽∈𝕍 : 𝔽 ∈ V 𝒦
 𝔽∈𝕍 = SP⊆V' 𝔽∈SP

\end{code}

#### <a id="the-hsp-theorem"> The HSP Theorem</a>

Now that we have all of the necessary ingredients, it is all but trivial to combine them to prove Birkhoff's HSP theorem.

\begin{code}

 birkhoff : Mod X (Th (V 𝒦)) ⊆ V 𝒦

 birkhoff {𝑨} α = γ
  where
   γ : 𝑨 ∈ (V 𝒦)
   γ = vhimg 𝔽∈𝕍 ((𝑨 , 𝔽-ModTh-epi 𝑨 α ) , refl-≅)

\end{code}

The converse inclusion, `V 𝒦 ⊆ Mod X (Th (V 𝒦))`, is a simple consequence of the fact that `Mod Th` is a closure operator. Nonetheless, completeness demands that we formalize this inclusion as well, however trivial the proof.

\begin{code}

 birkhoff' : V{𝓤}{𝓸𝓿𝓾} 𝒦 ⊆ Mod X (Th (V 𝒦))

 birkhoff' {𝑨} α p q pThq = pThq α

\end{code}

We have thus proved that every variety is an equational class.  Readers familiar with the classical formulation of the Birkhoff HSP theorem, as an "if and only if" result, might worry that we haven't completed the proof.  But recall that in the [Varieties.Preservation][] module we proved the following identity preservation lemmas:

* [(H-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#964) 𝒦 ⊧ p ≋ q → H 𝒦 ⊧ p ≋ q
* [(S-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#2592) 𝒦 ⊧ p ≋ q → S 𝒦 ⊧ p ≋ q
* [(P-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#4111) 𝒦 ⊧ p ≋ q → P 𝒦 ⊧ p ≋ q

From these it follows that every equational class is a variety. Thus, our formal proof of Birkhoff's theorem is complete.

----------------------------

<sup>1</sup> In the previous version of the [UALib][] this module was called HSPLemmas and the Birkhoff HSP theorem was in a separate module, while in the current version these are in the new HSPTheorem module.


[← UALib.Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
<span style="float:right;">[UALib.Birkhoff ↑](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}

