---
layout: default
title : UALib.Birkhoff.HSPTheorem (The Agda Universal Algebra Library)
date : 2021-02-02
author: William DeMeo
---

### <a id="hsp-theorem">HSP Theorem</a>

This section presents the [UALib.Birkhoff.HSPTheorem][] module of the [Agda Universal Algebra Library][].<sup>1</sup>

We begin the proof of Birkhoff's HSP theorem by establishing a number of facts that we will eventually string together in the HSPTheorem module to complete the proof.

(Unlike in previous modules, we fix 𝓤, X, and 𝒦 at the start of the HSPTheorem module.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇; _⊔_; _⁺; propext; hfunext)
open import UALib.Relations.Unary using (Pred)

module UALib.Birkhoff.HSPTheorem
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {𝓤 : Universe} {X : 𝓤 ̇}
 {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 -- extensionality assumptions:
    {pe : propext 𝓤}
    {pe' : propext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
    {hfe : hfunext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where

open import UALib.Birkhoff.FreeAlgebra {𝑆 = 𝑆}{gfe}{𝕏} hiding (Pred; _⊔_; _⁺; propext; hfunext) public
open the-free-algebra {𝓤}{𝓤}{X}

\end{code}


#### <a id="V-is-closed-under-lift">V is closed under lift</a>

The first hurdle is the `lift-alg-V-closure` lemma, which says that if an algebra 𝑨 belongs to the variety 𝕍, then so does its lift. This dispenses with annoying universe level problems that arise later---a minor techinical issue with a tedious, uninteresting proof.

\begin{code}

open Lift
lift-alg-V-closure -- (alias)
 VlA : {𝑨 : Algebra 𝓸𝓿𝓾 𝑆}
  →    𝑨 ∈ V{𝓤}{𝓸𝓿𝓾} 𝒦
       -------------------------------
  →    lift-alg 𝑨 𝓸𝓿𝓾+ ∈ V{𝓤}{𝓸𝓿𝓾+} 𝒦

VlA (vbase{𝑨} x) = visow (vbase x) (lift-alg-associative 𝑨)
VlA (vlift{𝑨} x) = visow (vlift x) (lift-alg-associative 𝑨)
VlA (vliftw{𝑨} x) = visow (VlA x) (lift-alg-associative 𝑨)
VlA (vhimg{𝑨}{𝑩} x hB) = vhimg (VlA x) (lift-alg-hom-image hB)
VlA (vssub{𝑨}{𝑩} x B≤A) = vssubw (vlift{𝓦 = 𝓸𝓿𝓾+} x) (lift-alg-≤ 𝑩{𝑨} B≤A)
VlA (vssubw{𝑨}{𝑩} x B≤A) = vssubw (VlA x) (lift-alg-≤ 𝑩{𝑨} B≤A)
VlA (vprodu{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
 where
  𝑰 : 𝓸𝓿𝓾+ ̇
  𝑰 = Lift{𝓸𝓿𝓾}{𝓸𝓿𝓾+} I

  lA+ : Algebra 𝓸𝓿𝓾+ 𝑆
  lA+ = lift-alg (⨅ 𝒜) 𝓸𝓿𝓾+

  lA : 𝑰 → Algebra 𝓸𝓿𝓾+ 𝑆
  lA i = lift-alg (𝒜 (lower i)) 𝓸𝓿𝓾+

  vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{𝓸𝓿𝓾+} 𝒦
  vlA i = vlift (x (lower i))

  iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
  iso-components i = lift-alg-≅

  B≅A : lA+ ≅ ⨅ lA
  B≅A = lift-alg-⨅≅ gfe iso-components

VlA (vprodw{I}{𝒜} x) = visow (vprodw vlA) (sym-≅ B≅A)
 where
  𝑰 : 𝓸𝓿𝓾+ ̇
  𝑰 = Lift{𝓸𝓿𝓾}{𝓸𝓿𝓾+} I

  lA+ : Algebra 𝓸𝓿𝓾+ 𝑆
  lA+ = lift-alg (⨅ 𝒜) 𝓸𝓿𝓾+

  lA : 𝑰 → Algebra 𝓸𝓿𝓾+ 𝑆
  lA i = lift-alg (𝒜 (lower i)) 𝓸𝓿𝓾+

  vlA : (i : 𝑰) → (lA i) ∈ V{𝓤}{𝓸𝓿𝓾+} 𝒦
  vlA i = VlA (x (lower i))

  iso-components : (i : I) → 𝒜 i ≅ lA (lift i)
  iso-components i = lift-alg-≅

  B≅A : lA+ ≅ ⨅ lA
  B≅A = lift-alg-⨅≅ gfe iso-components

VlA (visou{𝑨}{𝑩} x A≅B) = visow (vlift x) (lift-alg-iso 𝓤 𝓸𝓿𝓾+ 𝑨 𝑩 A≅B)
VlA (visow{𝑨}{𝑩} x A≅B) = visow (VlA x) (lift-alg-iso 𝓸𝓿𝓾 𝓸𝓿𝓾+ 𝑨 𝑩 A≅B)

lift-alg-V-closure = VlA -- (alias)

\end{code}

#### <a id="sp-in-v">SP(𝒦) ⊆ V(𝒦)</a>

In the [UALib.Varieties.Varieties][] module, we proved that `SP(𝒦) ⊆ V(𝒦)` holds with fairly general universe level parameters.  Unfortunately, this was not general enough for our purposes, so we prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.  This proof also suffers from the unfortunate defect of being boring.

\begin{code}

SP⊆V' : S{𝓸𝓿𝓾}{𝓸𝓿𝓾+} (P{𝓤}{𝓸𝓿𝓾} 𝒦) ⊆ V{𝓤}{𝓸𝓿𝓾+} 𝒦

SP⊆V' (sbase{𝑨} x) = γ
 where
  llA lA+ : Algebra 𝓸𝓿𝓾+ 𝑆
  lA+ = lift-alg 𝑨 𝓸𝓿𝓾+
  llA = lift-alg (lift-alg 𝑨 𝓸𝓿𝓾) 𝓸𝓿𝓾+

  vllA : llA ∈ V{𝓤}{𝓸𝓿𝓾+} 𝒦
  vllA = lift-alg-V-closure (SP⊆V (sbase x))

  llA≅lA+ : llA ≅ lA+
  llA≅lA+ = sym-≅ (lift-alg-associative 𝑨)

  γ : lA+ ∈ (V{𝓤}{𝓸𝓿𝓾+} 𝒦)
  γ = visow vllA llA≅lA+

SP⊆V' (slift{𝑨} x) = lift-alg-V-closure (SP⊆V x)
 -- ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦

SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw vlA B≤lA
 where
  lA : Algebra 𝓸𝓿𝓾+ 𝑆
  lA = lift-alg 𝑨 𝓸𝓿𝓾+

  vlA : lA ∈ V{𝓤}{𝓸𝓿𝓾+} 𝒦
  vlA = lift-alg-V-closure (SP⊆V spA)

  B≤lA : 𝑩 ≤ lA
  B≤lA = (lift-alg-lower-≤-lift {𝓸𝓿𝓾+}{𝓸𝓿𝓾}{𝓸𝓿𝓾+} 𝑩 {𝑨}) B≤A

SP⊆V' (ssubw{𝑨}{𝑩} spA B≤A) = vssubw (SP⊆V' spA) B≤A

SP⊆V' (siso{𝑨}{𝑩} x A≅B) = visow (lift-alg-V-closure vA) lA≅B
 where
  lA : Algebra 𝓸𝓿𝓾+ 𝑆
  lA = lift-alg 𝑨 𝓸𝓿𝓾+

  plA : 𝑨 ∈ S{𝓸𝓿𝓾}{𝓸𝓿𝓾}(P{𝓤}{𝓸𝓿𝓾} 𝒦)
  plA = x

  vA : 𝑨 ∈ V{𝓤}{𝓸𝓿𝓾} 𝒦
  vA = SP⊆V x

  lA≅B : lA ≅ 𝑩
  lA≅B = Trans-≅ lA 𝑩 (sym-≅ lift-alg-≅) A≅B

\end{code}

#### <a id="F-in-classproduct">𝔉 ≤  ⨅ S(𝒦)</a>
Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial. We must prove that the free algebra 𝔉 embeds in the product ℭ of all subalgebras of algebras in the class 𝒦.  This is really the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that ℭ be a set.

We begin by constructing ℭ, using the class-product types described in the section on <a href="https://ualib.gitlab.io/UALib.Varieties.Varieties.html#products-of-classes">products of classes</a>.

\begin{code}

open the-relatively-free-algebra {𝓤 = 𝓤}{𝓧 = 𝓤}{X = X} {𝒦 = 𝒦}
-- open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}

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

ker-incl-lem : {p q : ∣ 𝑻 X ∣} → (∀ i → (p , q) ∈ KER-pred ∣ T𝔄 i ∣)
 →             (p , q) ∈ ψ 𝒦
ker-incl-lem hyp 𝑨 sA h = hyp (𝑨 , (sA , h))

𝔽 : Algebra 𝓸𝓿𝓾+ 𝑆
𝔽 = (𝑻 X) [ ℭ ]/ker ΨTC

Ψe : epi (𝑻 X) 𝔽
Ψe = πker (𝑻 X) {ℭ} ΨTC

Ψ : hom (𝑻 X) 𝔽
Ψ = epi-to-hom 𝔽 Ψe


ker-incl-lem' : ∀ p q → (p , q) ∈ KER-pred ∣ Ψ ∣
 →             (∀ i → (p , q) ∈ KER-pred ∣ T𝔄 i ∣)
ker-incl-lem' p q hyp i =
 ∣ T𝔄 i ∣ p ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
 (∣ ΨTC ∣ p) i ≡⟨ γ ⟩
 (∣ ΨTC ∣ q) i ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
 ∣ T𝔄 i ∣ q    ∎
  where
   H₀ : ∣ Ψ ∣ p ≡ ∣ Ψ ∣ q
   H₀ = hyp
   ξ : ∣ ΨTC ∣ p ≡ ∣ ΨTC ∣ q
   ξ = ker-in-con (𝑻 X) (kercon (𝑻 X) {ℭ} ΨTC) p q H₀
   γ : ∣ ΨTC ∣ p i ≡ ∣ ΨTC ∣ q i
   γ = ap (λ - → - i) ξ


ΨE : Epic ∣ Ψ ∣
ΨE = snd ∥ Ψe ∥

X↪𝔽 : X → ∣ 𝔽 ∣
X↪𝔽 x = ⟦ ℊ x ⟧


KER-incl' : {𝑨 : Algebra 𝓤 𝑆}{h : X → ∣ 𝑨 ∣} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → KER-pred ∣ Ψ ∣ ⊆ KER-pred (free-lift 𝑨 h)
KER-incl' {𝑨}{h} skA {p , q} x = (ker-incl-lem {p}{q} (ker-incl-lem' p q x)) 𝑨 skA h


--KER-incl {𝑨}{h} skA {p , q} {!!} -- (ker-incl-lemma x)


𝔽-lift-hom : (𝑨 : Algebra 𝓤 𝑆) → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → (X → ∣ 𝑨 ∣) → hom 𝔽 𝑨
𝔽-lift-hom 𝑨 skA h = fst (HomFactor gfe (𝑻 X) {𝑨}{𝔽} (lift-hom 𝑨 h) Ψ ΨE (KER-incl' {𝑨}{h} skA))

Ψ-is-lift-hom : ∀ p → ∣ lift-hom 𝔽 X↪𝔽 ∣ p ≡ ∣ Ψ ∣ p
Ψ-is-lift-hom (ℊ x) = 𝓇ℯ𝒻𝓁
Ψ-is-lift-hom (node f args) = let g = ∣ lift-hom 𝔽 X↪𝔽 ∣ in
   g (node f args)               ≡⟨ ∥ lift-hom 𝔽 X↪𝔽 ∥ f args ⟩
   (f ̂ 𝔽)(λ i → g (args i))      ≡⟨ ap (f ̂ 𝔽) (gfe (λ x → Ψ-is-lift-hom (args x))) ⟩
   (f ̂ 𝔽)(λ i → ∣ Ψ ∣ (args i)) ≡⟨ (∥ Ψ ∥ f args)⁻¹ ⟩
   ∣ Ψ ∣ (node f args)          ∎


ψlemma1 : ∀ p q → (free-lift 𝔽 X↪𝔽) p ≡ (free-lift 𝔽 X↪𝔽) q → (p , q) ∈ ψ 𝒦
ψlemma1 p q gpq 𝑨 sA h = γ
   where
    g : hom (𝑻 X) 𝔽
    g = lift-hom 𝔽 (X↪𝔽)

    f : hom 𝔽 𝑨
    f = 𝔽-lift-hom 𝑨 sA h

    h' ϕ : hom (𝑻 X) 𝑨
    h' = HomComp (𝑻 X) 𝑨 g f
    ϕ = lift-hom 𝑨 h

    --homs from 𝑻 X to 𝑨 that agree on X are equal
    fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
    fgx≡ϕ x = 𝓇ℯ𝒻𝓁
    h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
    h≡ϕ t = free-unique gfe 𝑨 h' ϕ fgx≡ϕ t

    γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
    γ = ∣ ϕ ∣ p         ≡⟨ (h≡ϕ p)⁻¹ ⟩
        ∣ f ∣ ( ∣ g ∣ p ) ≡⟨ ap ∣ f ∣ gpq ⟩
        ∣ f ∣ ( ∣ g ∣ q ) ≡⟨ h≡ϕ q ⟩
        ∣ ϕ ∣ q ∎

ψlemma2 : KER-pred ∣ Ψ ∣ ⊆ ψ 𝒦
ψlemma2 {p , q} hyp = ψlemma1 p q γ
  where
   γ : ∣ lift-hom 𝔽 X↪𝔽 ∣ p ≡ ∣ lift-hom 𝔽 X↪𝔽 ∣ q
   γ = (Ψ-is-lift-hom p) ∙ hyp ∙ (Ψ-is-lift-hom q)⁻¹

ψlemma3 : ∀ p q → (p , q) ∈ ψ 𝒦 → 𝒦 ⊧ p ≋ q
ψlemma3 p q pψq {𝑨} kA = γ
 where
  skA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦
  skA = siso (sbase kA) (sym-≅ lift-alg-≅)

  γ : (p ̇ 𝑨) ≡ (q ̇ 𝑨)
  γ = gfe λ h → (p ̇ 𝑨) h ≡⟨ free-lift-interp 𝑨 h p ⟩
                (free-lift 𝑨 h) p ≡⟨ pψq 𝑨 skA h ⟩
                (free-lift 𝑨 h) q ≡⟨ (free-lift-interp 𝑨 h q)⁻¹  ⟩
                (q ̇ 𝑨) h ∎

class-models-kernel : ∀ p q → (p , q) ∈ KER-pred ∣ Ψ ∣ → 𝒦 ⊧ p ≋ q
class-models-kernel  p q hyp = ψlemma3 p q (ψlemma2 hyp)

kernel-in-theory : KER-pred ∣ Ψ ∣ ⊆ Th (V 𝒦)
kernel-in-theory {p , q} pKq = (class-ids-⇒ p q (class-models-kernel p q pKq))

\end{code}

Finally we come to one of the main theorems of this module; it asserts that every algebra in `Mod X (Th 𝕍𝒦)` is a homomorphic image of 𝔉.

\begin{code}

open Congruence
free-quot-subalg-ℭ : is-set ∣ ℭ ∣
 →                   (∀ p q → is-subsingleton (⟨ kercon (𝑻 X){ℭ} ΨTC ⟩ p q))
 →                   (∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon (𝑻 X){ℭ} ΨTC ⟩} C))
                     -------------------------------------------------------------------
 →                   ((𝑻 X) [ ℭ ]/ker ΨTC) ≤ ℭ

free-quot-subalg-ℭ Cset ssR ssC = FirstHomCorollary (𝑻 X) ℭ ΨTC pe' Cset ssR ssC


module _ (Cset : is-set ∣ ℭ ∣)
         (ssR : ∀ p q → is-subsingleton (⟨ kercon (𝑻 X){ℭ} (ΨTC) ⟩ p q))
         (ssC : ∀ C → is-subsingleton (𝒞{A = ∣ 𝑻 X ∣}{⟨ kercon (𝑻 X){ℭ}  (ΨTC ) ⟩} C)) where

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
   γ = fst (HomFactorEpi gfe (𝑻 X){𝑨}{𝔽} ϕ ϕE Ψ ΨE  kerincl)


\end{code}

#### 𝔉 ∈ V(𝒦)

Now, with this result in hand, along with what we proved earlier---namely, PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦---it is not hard to show that 𝔉 belongs to SP(𝒦), and hence to V 𝒦. (Recall, if 𝒦 denotes a class of 𝑆-algebras, then the variety generated 𝒦 is `V 𝒦`, which is equivalent to HSP 𝒦.)

\begin{code}

 𝔽∈SP : 𝔽 ∈ (S{𝓸𝓿𝓾}{𝓸𝓿𝓾+} (P{𝓤}{𝓸𝓿𝓾} 𝒦))
 𝔽∈SP = ssub (class-prod-s-∈-sp hfe) 𝔽≤ℭ

 𝔽∈𝕍 : 𝔽 ∈ V 𝒦
 𝔽∈𝕍 = SP⊆V' 𝔽∈SP

 birkhoff : Mod X (Th (V 𝒦)) ⊆ (V 𝒦)

 birkhoff {𝑨} α = γ
  where
   ϕ : epi 𝔽 𝑨
   ϕ = 𝔽-ModTh-epi 𝑨 α

   AiF : 𝑨 is-hom-image-of 𝔽
   AiF = (𝑨 , ϕ ) , refl-≅

   γ : 𝑨 ∈ (V 𝒦)
   γ = vhimg 𝔽∈𝕍 AiF

\end{code}

Some readers might worry that we haven't quite acheived our goal because what we just proved (<a href="https://ualib.gitlab.io/UALib.Birkhoff.Theorem.html#1487">birkhoff</a>) is not an "if and only if" assertion. Those fears are quickly put to rest by noting that the converse---that every equational class is closed under HSP---was already proved in the [Equation Preservation](UALib.Varieties.Preservation.html) module. Indeed, there we proved the following identity preservation lemmas:

* [(H-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#964) 𝒦 ⊧ p ≋ q → H 𝒦 ⊧ p ≋ q
* [(S-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#2592) 𝒦 ⊧ p ≋ q → S 𝒦 ⊧ p ≋ q
* [(P-id1)](https://ualib.gitlab.io/UALib.Varieties.Preservation.html#4111) 𝒦 ⊧ p ≋ q → P 𝒦 ⊧ p ≋ q

From these it follows that every equational class is a variety.

----------------------------

<sup>1</sup> In the previous version of the [UALib][] this module was called HSPLemmas and the Birkhoff HSP theorem was in a separate module, while in the current version these are in the new HSPTheorem module.


[← UALib.Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
<span style="float:right;">[UALib.Birkhoff ↑](UALib.Birkhoff.html)</span>

{% include UALib.Links.md %}

