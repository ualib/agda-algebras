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

In earlier versions of the [Agda UALib][], the free algebra 𝔉 developed in the [Birkhoff.FreeAlgebra][] section played the role of the algebra 𝔽 with properties 1 and 2.  However, we found a more direct path to the proof using the algebra `𝔽 := (𝑻 X) [ ℭ ]/ker homℭ`. 

Here, ℭ denotes the product of all subalgebras of algebras in 𝒦, and `homℭ` denotes the homomorphism from `𝑻 X` to `ℭ` defined by

`homℭ := ⨅-hom-co (𝑻 X) (λ i → (hom𝔄 i))`.

Recall, `⨅-hom-co` (defined in [Homomorphisms.Basic](UALib.Homomorphisms.Basic.html#product-homomorphisms)) takes an 𝑆-algebra `𝑨`, a family `{𝔄 : I → Algebra 𝓤 𝑆}` of 𝑆-algebras, and a family `hom𝔄 : ∀ i → hom 𝑨 (𝔄 i)` of homomorphisms and constructs the natural homomorphism `homℭ` from `𝑨` to the product `ℭ := ⨅ 𝔄`.  The homomorphism `homℭ : hom 𝑨 (⨅ ℭ)` is natural in the sense that the `i`-th component of the image of `𝑎 : ∣ 𝑨 ∣` under `homℭ` is the image `∣ hom𝔄 i ∣ 𝑎` of 𝑎 under the i-th homomorphism `hom𝔄 i`.

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

We begin by constructing ℭ, using the techniques described in the section on <a href="https://ualib.gitlab.io/UALib.Varieties.Varieties.html#products-of-classes">products of classes</a>.

**Notation**. In this module, the type `ℑs` will index the collection of all subalgebras of algebras in the class 𝒦, and `𝔄s : ℑs → Algebra 𝓤 𝑆` will be a map from the index type to the subalgebras. 

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

hom𝔄 : ∀ i → hom (𝑻 X) (𝔄s i)
hom𝔄 i = lift-hom (𝔄s i) (𝔄h i)

homℭ : hom (𝑻 X) ℭ
homℭ = ⨅-hom-co gfe (𝑻 X) {ℑs}{𝔄s}(λ i → (hom𝔄 i))

\end{code}


#### <a id="the-new-free-algebra">The new free algebra</a>

As mentioned above, the initial version of the [Agda UALib][] used the free algebra `𝔉`, developed in the [Birkhoff.FreeAlgebra][] module.  However, our new, more direct proof uses the algebra `𝔽`, which we now define, along with the natural epimorphism `epi𝔽 : epi (𝑻 X) 𝔽` from `𝑻 X` to `𝔽`.<sup>2</sup>

\begin{code}

𝔽 : Algebra 𝓸𝓿𝓾+ 𝑆
𝔽 = (𝑻 X) [ ℭ ]/ker homℭ

epi𝔽 : epi (𝑻 X) 𝔽
epi𝔽 = πker ℭ homℭ

hom𝔽 : hom (𝑻 X) 𝔽
hom𝔽 = epi-to-hom 𝔽 epi𝔽

hom𝔽-is-epic : Epic ∣ hom𝔽 ∣
hom𝔽-is-epic = snd ∥ epi𝔽 ∥

\end{code}

We will need the following facts relating homℭ, hom𝔽, and ψ.

\begin{code}

ψlemma0 : ∀ p q → (∣ homℭ ∣ p ≡ ∣ homℭ ∣ q) → (p , q) ∈ ψ 𝒦
ψlemma0 p q phomℭq 𝑨 sA h = ap (λ - → - (𝑨 , (sA , h))) phomℭq


ψlemma0-ap : {𝑨 : Algebra 𝓤 𝑆}{h : X → ∣ 𝑨 ∣}
 →           𝑨 ∈ S{𝓤}{𝓤} 𝒦
             ---------------------------------------
 →           KER-pred ∣ hom𝔽 ∣ ⊆ KER-pred (free-lift 𝑨 h)

ψlemma0-ap {𝑨}{h} skA {p , q} x = γ where

  ν : ∣ homℭ ∣ p ≡ ∣ homℭ ∣ q
  ν = ker-in-con (𝑻 X) (kercon ℭ homℭ) p q x

  γ : (free-lift 𝑨 h) p ≡ (free-lift 𝑨 h) q
  γ = ((ψlemma0 p q) ν) 𝑨 skA h


\end{code}

We now use `ψlemma0-ap` to prove that every map `h : X → ∣ 𝑨 ∣`, from `X` to a subalgebra `𝑨 ∈ S 𝒦` of `𝒦`, lifts to a homomorphism from `𝔽` to `𝑨`.

\begin{code}

𝔽-lift-hom : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
𝔽-lift-hom 𝑨 skA h = fst(HomFactor (𝑻 X){𝑨}{𝔽}(lift-hom 𝑨 h) hom𝔽 hom𝔽-is-epic (ψlemma0-ap skA))

\end{code}


#### <a id="k-models-psi">𝒦 models ψ</a>

The goal of this subsection is to prove that `𝒦` models `ψ 𝒦`. In other terms, for all pairs `(p , q) ∈ Term X × Term X` of terms, if `(p , q) ∈ ψ 𝒦`, then `𝒦 ⊧ p ≋ q`.

Next we define the lift of the natural embedding from `X` into 𝔽. We denote this homomorphism by `𝔑 : hom (𝑻 X) 𝔽` and define it as follows.

\begin{code}

X↪𝔽 : X → ∣ 𝔽 ∣
X↪𝔽 x = ⟦ ℊ x ⟧

𝔑 : hom (𝑻 X) 𝔽
𝔑 = lift-hom 𝔽 X↪𝔽

\end{code}

It turns out that the homomorphism so defined is equivalent to `hom𝔽`.

\begin{code}

hom𝔽-is-lift-hom : ∀ p → ∣ 𝔑 ∣ p ≡ ∣ hom𝔽 ∣ p
hom𝔽-is-lift-hom (ℊ x) = 𝓇ℯ𝒻𝓁
hom𝔽-is-lift-hom (node 𝑓 𝒕) = ∣ 𝔑 ∣ (node 𝑓 𝒕)           ≡⟨ ∥ 𝔑 ∥ 𝑓 𝒕 ⟩
                          (𝑓 ̂ 𝔽)(λ i → ∣ 𝔑 ∣(𝒕 i))  ≡⟨ ap(𝑓 ̂ 𝔽)(gfe (λ x → hom𝔽-is-lift-hom(𝒕 x))) ⟩
                          (𝑓 ̂ 𝔽)(λ i → ∣ hom𝔽 ∣ (𝒕 i))  ≡⟨ (∥ hom𝔽 ∥ 𝑓 𝒕)⁻¹ ⟩
                          ∣ hom𝔽 ∣ (node 𝑓 𝒕)           ∎


\end{code}

We need a three more lemmas before we are ready to tackle our main goal.

\begin{code}

ψlemma1 : KER-pred ∣ 𝔑 ∣ ⊆ ψ 𝒦
ψlemma1 {p , q} 𝔑pq 𝑨 sA h = γ
 where
  f : hom 𝔽 𝑨
  f = 𝔽-lift-hom 𝑨 sA h

  h' ϕ : hom (𝑻 X) 𝑨
  h' = HomComp (𝑻 X) 𝑨 𝔑 f
  ϕ = lift-hom 𝑨 h

  f𝔑≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ 𝔑 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
  f𝔑≡ϕ x = 𝓇ℯ𝒻𝓁
  h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ 𝔑 ∣) t ≡ ∣ ϕ ∣ t
  h≡ϕ t = free-unique gfe 𝑨 h' ϕ f𝔑≡ϕ t

  γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
  γ = ∣ ϕ ∣ p         ≡⟨ (h≡ϕ p)⁻¹ ⟩
      ∣ f ∣ ( ∣ 𝔑 ∣ p ) ≡⟨ ap ∣ f ∣ 𝔑pq ⟩
      ∣ f ∣ ( ∣ 𝔑 ∣ q ) ≡⟨ h≡ϕ q ⟩
      ∣ ϕ ∣ q ∎


ψlemma2 : KER-pred ∣ hom𝔽 ∣ ⊆ ψ 𝒦
ψlemma2 {p , q} hyp = ψlemma1 {p , q} γ
  where
   γ : (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q
   γ = (hom𝔽-is-lift-hom p) ∙ hyp ∙ (hom𝔽-is-lift-hom q)⁻¹


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


\end{code}

With these results in hand, it is now trivial to prove the main theorem of this subsection.

\begin{code}

class-models-kernel : ∀ p q → (p , q) ∈ KER-pred ∣ hom𝔽 ∣ → 𝒦 ⊧ p ≋ q
class-models-kernel  p q hyp = ψlemma3 p q (ψlemma2 hyp)

\end{code}


#### <a id="the-homomorphic-images-of-F">The homomorphic images of 𝔽</a>

Finally we come to one of the main theorems of this module; it asserts that every algebra in `Mod X (Th 𝕍𝒦)` is a homomorphic image of 𝔽.  We prove this below as the function (or proof object) `𝔽-ModTh-epi`.  Before that, we prove two auxiliary lemmas.

\begin{code}

kernel-in-theory : KER-pred ∣ hom𝔽 ∣ ⊆ Th (V 𝒦)
kernel-in-theory {p , q} pKq = (class-ids-⇒ p q (class-models-kernel p q pKq))

open Congruence
free-quot-subalg-ℭ : is-set ∣ ℭ ∣
 →                   (∀ p q → is-subsingleton (⟨ kercon ℭ homℭ ⟩ p q))
 →                   (∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon ℭ homℭ ⟩} C))
                     -----------------------------------------------------------
 →                   ((𝑻 X) [ ℭ ]/ker homℭ) ≤ ℭ

free-quot-subalg-ℭ Cset ssR ssC = FirstHomCorollary (𝑻 X) ℭ homℭ pe' Cset ssR ssC


module _ (Cset : is-set ∣ ℭ ∣)
         (ssR : ∀ p q → is-subsingleton (⟨ kercon ℭ homℭ ⟩ p q))
         (ssC : ∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon ℭ homℭ ⟩} C)) where

 𝔽≤ℭ : ((𝑻 X) [ ℭ ]/ker homℭ) ≤ ℭ
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

   pqlem2 : ∀ p q → (p , q) ∈ KER-pred ∣ hom𝔽 ∣ → 𝑨 ⊧ p ≈ q
   pqlem2 p q hyp = AinMTV p q (kernel-in-theory hyp)

   kerincl : KER-pred ∣ hom𝔽 ∣ ⊆ KER-pred ∣ ϕ ∣
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
   γ = fst (HomFactorEpi (𝑻 X){𝑨}{𝔽} ϕ ϕE hom𝔽 hom𝔽-is-epic  kerincl)


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

<sup>2</sup> It might be an instructive exercise to prove that 𝔽 is, in fact, isomorphic to the free algebra 𝔉 that we defined in the [UALib.Birkhoff.FreeAlgebra][] module.


[← UALib.Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
<span style="float:right;">[UALib.Birkhoff ↑](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}

