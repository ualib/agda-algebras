---
layout: default
title : UALib.Birkhoff.HSPLemmas (The Agda Universal Algebra Library)
date : 2021-02-02
author: William DeMeo
---

### <a id="hsp-lemmas">HSP Lemmas</a>

This section presents the [UALib.Birkhoff.HSPLemmas][] module of the [Agda Universal Algebra Library][].

We begin the proof of Birkhoff's HSP theorem by establishing a number of facts that we will eventually string together in the HSPTheorem module to complete the proof.  
**Warning**: not all of these are very interesting!

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇; _⊔_; _⁺; propext; hfunext)
open import UALib.Relations.Unary using (Pred)

module UALib.Birkhoff.HSPLemmas
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {𝓤 : Universe} {X : 𝓤 ̇} {𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
 -- extensionality assumptions:
    {pe : propext 𝓤}
    {pe' : propext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)}
    {hfe : hfunext (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where


open import UALib.Birkhoff.FreeAlgebra {𝑆 = 𝑆}{gfe}{𝕏} hiding (Pred; _⊔_; _⁺; propext; hfunext) public

open the-free-algebra {𝓤}{𝓤}{X}


-- NOTATION.
ovu ovu+ : Universe
ovu = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
ovu+ = ovu ⁺

\end{code}


#### <a id="V-is-closed-under-lift">V is closed under lift</a>

The first hurdle is the `lift-alg-V-closure` lemma, which says that if an algebra 𝑨 belongs to the variety 𝕍, then so does its lift. This dispenses with annoying universe level problems that arise later---a minor techinical issue with a tedious, uninteresting proof.

\begin{code}

open Lift
lift-alg-V-closure -- (alias)
 VlA : {𝑨 : Algebra ovu 𝑆}
  →    𝑨 ∈ V{𝓤}{ovu} 𝒦
       -------------------------------
  →    lift-alg 𝑨 ovu+ ∈ V{𝓤}{ovu+} 𝒦

VlA (vbase{𝑨} x) = visow (vbase{𝓤}{𝓦 = ovu+} x) (lift-alg-associative 𝑨)
VlA (vlift{𝑨} x) = visow (vlift{𝓤}{𝓦 = ovu+} x) (lift-alg-associative 𝑨)
VlA (vliftw{𝑨} x) = visow (VlA x) (lift-alg-associative 𝑨)
VlA (vhimg{𝑨}{𝑩} x hB) = vhimg (VlA x) (lift-alg-hom-image hB)
VlA (vssub{𝑨}{𝑩} x B≤A) = vssubw (vlift{𝓤}{𝓦 = ovu+} x) (lift-alg-≤ 𝑩{𝑨} B≤A)
VlA (vssubw{𝑨}{𝑩} x B≤A) = vssubw (VlA x) (lift-alg-≤ 𝑩{𝑨} B≤A)
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

VlA (visou{𝑨}{𝑩} x A≅B) = visow (vlift x) (lift-alg-iso 𝓤 ovu+ 𝑨 𝑩 A≅B)
VlA (visow{𝑨}{𝑩} x A≅B) = visow (VlA x) (lift-alg-iso ovu ovu+ 𝑨 𝑩 A≅B)

lift-alg-V-closure = VlA -- (alias)

\end{code}

#### <a id="sp-in-v">SP(𝒦) ⊆ V(𝒦)</a>

In the [UALib.Varieties.Varieties][] module, we proved that `SP(𝒦) ⊆ V(𝒦)` holds with fairly general universe level parameters.  Unfortunately, this was not general enough for our purposes, so we prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.  This proof also suffers from the unfortunate defect of being boring.

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
 -- ssub  : {𝑨 : Algebra 𝓤 𝑆}{𝑩 : Algebra _ 𝑆} → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → 𝑩 ≤ 𝑨 → 𝑩 ∈ S 𝒦

SP⊆V' (ssub{𝑨}{𝑩} spA B≤A) = vssubw vlA B≤lA
 where
  lA : Algebra ovu+ 𝑆
  lA = lift-alg 𝑨 ovu+

  vlA : lA ∈ V{𝓤}{ovu+} 𝒦
  vlA = lift-alg-V-closure (SP⊆V spA)

  B≤lA : 𝑩 ≤ lA
  B≤lA = (lift-alg-lower-≤-lift {ovu+}{ovu}{ovu+} 𝑩 {𝑨}) B≤A

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

#### <a id="F-in-classproduct">𝔉 ≤  ⨅ S(𝒦)</a>
Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial. We must prove that the free algebra 𝔉 embeds in the product ℭ of all subalgebras of algebras in the class 𝒦.  This is really the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that ℭ be a set.

We begin by constructing ℭ, using the class-product types described in the section on <a href="https://ualib.gitlab.io/UALib.Varieties.Varieties.html#products-of-classes">products of classes</a>.

\begin{code}

open the-relatively-free-algebra {𝓤 = 𝓤}{𝓧 = 𝓤}{X = X} {𝒦 = 𝒦}
open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}

-- NOTATION.
ℑs : ovu ̇
ℑs = ℑ (S{𝓤}{𝓤} 𝒦)

𝔄s : ℑs → Algebra 𝓤 𝑆
𝔄s = λ (i : ℑs) → ∣ i ∣

SK𝔄 : (i : ℑs) → (𝔄s i) ∈ S{𝓤}{𝓤} 𝒦
SK𝔄 = λ (i : ℑs) → ∥ i ∥

-- ℭ is the product of all subalgebras of algebras in 𝒦.
ℭ : Algebra ovu 𝑆
ℭ = ⨅ 𝔄s

\end{code}

Observe that the inhabitants of ℭ are maps from ℑs to {𝔄s i : i ∈ ℑs}.

The next function we define is a homomorphism `𝔣 : hom 𝔉 ℭ`. It is constructed as follows: if we are given a family h𝔄 : ∀ i → X → (𝔄s i) of maps from X to algebras in 𝔄s, then 𝔣 is the product of homomorphisms `ϕ𝔄 : ∀ i → 𝔉-lift-hom (𝔄s i)(SK𝔄 i) (h𝔄 i)`.

\begin{code}

-- ϕ𝔄 : (∀ i → X → ∣ 𝔄s i ∣) → ∀ i → hom 𝔉 (𝔄s i)
-- ϕ𝔄 h𝔄 i = 𝔉-lift-hom (𝔄s i)(SK𝔄 i) (h𝔄 i)

ϕ𝔄 : ∀ i → (X → ∣ 𝔄s i ∣) → hom 𝔉 (𝔄s i)
ϕ𝔄 i h𝔄 = 𝔉-lift-hom (𝔄s i)(SK𝔄 i) h𝔄

𝔣 : (∀ i → X → ∣ 𝔄s i ∣) → hom 𝔉 ℭ
𝔣 h𝔄 = ⨅-hom-co gfe 𝔉 {ℑs}{𝔄s}(λ i → (ϕ𝔄 i)(h𝔄 i))
--old versions:
-- 𝔣 : hom 𝔉 ℭ
-- 𝔣 = 𝔉-lift-hom ℭ 𝔥₀ , λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝)
-- 𝔣 = 𝔉-lift-hom ℭ , λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝)

𝔤 : hom (𝑻 X) 𝔉
𝔤 = lift-hom 𝔉 (X↪𝔉)

𝔤-agrees-on-X : ∀ x → ∣ 𝔤 ∣ (ℊ x) ≡ ⟦ ℊ x ⟧
𝔤-agrees-on-X = λ x → 𝓇ℯ𝒻𝓁

𝔤-⟦⟧ : ∀ p → ∣ 𝔤 ∣ p ≡ ⟦ p ⟧
𝔤-⟦⟧ p = π𝔉-X-defined 𝔤 𝔤-agrees-on-X p

-- πℭ i is the projection out of the product ℭ onto the i-th factor.
πℭ : (i : ℑs) → ∣ ℭ ∣ → ∣ 𝔄s i ∣
πℭ i 𝒂 = 𝒂 i

πℭhom : (i : ℑs) → hom ℭ (𝔄s i)
πℭhom = ⨅-projection-hom {I = ℑs}{𝒜 = 𝔄s}

 --
 --                             𝔄1
 --                            77
 --                           /
 --        𝑻 -----ϕ≡h --->>  ℭ -->> 𝔄2
 --         \             77        ⋮
 --          \           /
 --           g         ∃f
 --            \       /
 --             \     /
 --              V  l/
 --             𝔉 = 𝑻/ψ

πℭ𝔣hom :  (𝔥 : ∀ i → X → ∣ 𝔄s i ∣) → (i : ℑs) → hom 𝔉 (𝔄s i)
πℭ𝔣hom 𝔥 i = HomComp 𝔉 (𝔄s i) (𝔣 𝔥) (πℭhom i)

\end{code}

Armed with these tools, we proceed to the proof that the free algebra 𝔉 is a subalgebra of the product ℭ of all subalgebras of algebras in 𝒦.  The hard part of the proof is showing that `𝔣 : hom 𝔉 ℭ` is a monomorphism. Let's dispense with that first.

\begin{code}

R : Rel ∣ 𝑻 X ∣ (ov 𝓤)
R = ψRel 𝒦

mon𝔣 : (𝔥 : ∀ i → X → ∣ 𝔄s i ∣) →  (∀ i → Monic (𝔥 i))
       -- truncation assumptions:
 →        (ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q))
          (ssA : ∀ C → is-subsingleton (𝒞{ov 𝓤}{ov 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C))
       -------------------------------------------------------------------
 →     Monic ∣ 𝔣 𝔥 ∣

mon𝔣 𝔥 𝔥M ssR ssA (.(R p) , p , refl _) (.(R q) , q , refl _) fpq = γ
 where
   -- lem : ∀ 𝑨 → 𝑨 ∈ S{𝓤}{𝓤} 𝒦 → p ̇ 𝑨 ≡ q ̇ 𝑨
   -- lem = {!!}
  pRq : R p q
  pRq 𝑨 sA h' = γ'

 -- Recall, ψ 𝒦 (p , q) = ∀(𝑨 : Algebra 𝓤 𝑆)(sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦)(h : X → ∣ 𝑨 ∣ )
 --                 →  ∣ lift-hom 𝑨 h ∣ p ≡ ∣ lift-hom 𝑨 h ∣ q
 -- So we must show ∣ lift-hom 𝑨 h ∣ p ≡ ∣ lift-hom 𝑨 h ∣ q.

   where
    πℭA : hom 𝔉 𝑨
    πℭA = πℭ𝔣hom 𝔥 (𝑨 , sA)

    𝔣pq : ∣ πℭA ∣ ⟦ p ⟧ ≡ ∣ πℭA ∣ ⟦ q ⟧
    𝔣pq = ∣ πℭA ∣ ⟦ p ⟧                    ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ πℭhom (𝑨 , sA) ∣ ( ∣ 𝔣 𝔥 ∣ ⟦ p ⟧ ) ≡⟨ ap (λ - → (∣ πℭhom (𝑨 , sA) ∣ -)) fpq ⟩
          ∣ πℭhom (𝑨 , sA) ∣ ( ∣ 𝔣 𝔥 ∣ ⟦ q ⟧ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ πℭA ∣ ⟦ q ⟧                     ∎

    h ϕ : hom (𝑻 X) 𝑨
    h = HomComp (𝑻 X) 𝑨 𝔤 πℭA
    ϕ = lift-hom 𝑨 ((πℭ (𝑨 , sA)) ∘ (λ x i → 𝔥 i x))
    hh' : hom (𝑻 X) 𝑨
    hh' = lift-hom 𝑨 h'

    𝔣gx≡ϕ : (x : X) → (∣ πℭA ∣ ∘ ∣ 𝔤 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
    𝔣gx≡ϕ x = ∣ πℭA ∣ (∣ 𝔤 ∣ (ℊ x)) ≡⟨ ap ∣ πℭA ∣ (𝔤-⟦⟧ (ℊ x)) ⟩
              ∣ πℭA ∣ (⟦ ℊ x ⟧)   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
              ∣ ϕ ∣ (ℊ x)        ∎

    h≡ϕ' : ∀ t → (∣ πℭA ∣ ∘ ∣ 𝔤 ∣) t ≡ ∣ ϕ ∣ t
    h≡ϕ' t = free-unique gfe 𝑨 h ϕ 𝔣gx≡ϕ t
 -- π𝔉 : hom (𝑻 X) 𝔉
 -- π𝔉 = epi-to-hom 𝔉 𝔉-canonical-epi

    hyp : KER-pred ∣ π𝔉 ∣ (p , q)
    hyp = ∣ π𝔉 ∣ p ≡⟨ (π𝔉-is-lift-hom p)⁻¹ ⟩
          ∣ lift-hom 𝔉 X↪𝔉 ∣ p ≡⟨ {!fpq!} ⟩
          ∣ lift-hom 𝔉 X↪𝔉 ∣ q ≡⟨ π𝔉-is-lift-hom q ⟩
          ∣ π𝔉 ∣ q  ∎


    γ' : free-lift 𝑨 h' p ≡ free-lift 𝑨 h' q
    γ' = {!!} -- KER-incl{𝑨}{h'} sA hyp
          -- ∣ ϕ ∣ p            ≡⟨ (h≡ϕ' p)⁻¹ ⟩
          -- ∣ πℭA ∣ ( ∣ 𝔤 ∣ p ) ≡⟨ ap ∣ πℭA ∣ (𝔤-⟦⟧ p) ⟩
          -- ∣ πℭA ∣ ⟦ p ⟧       ≡⟨ 𝔣pq ⟩
          -- ∣ πℭA ∣ ⟦ q ⟧       ≡⟨ (ap ∣ πℭA ∣ (𝔤-⟦⟧ q))⁻¹ ⟩
          -- ∣ πℭA ∣ ( ∣ 𝔤 ∣ q ) ≡⟨ h≡ϕ' q ⟩
          -- ∣ ϕ ∣ q            ∎

  γ : ( R p , p , 𝓇ℯ𝒻𝓁) ≡ ( R q , q , 𝓇ℯ𝒻𝓁)
  γ = class-extensionality' pe' gfe ssR ssA ψIsEquivalence pRq

\end{code}

With that out of the way, the proof that 𝔉 is (isomorphic to) a subalgebra of ℭ is all but complete.

\begin{code}
𝔉≤ℭ : (𝔥 : ∀ i → X → ∣ 𝔄s i ∣) → (∀ i → Monic (𝔥 i))
       -- truncation assumptions:
 →        is-set ∣ ℭ ∣
 →        (ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q))
          (ssA : ∀ C → is-subsingleton (𝒞{ov 𝓤}{ov 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C))
       --------------------------------------------------------------------
 →     𝔉 ≤ ℭ

𝔉≤ℭ 𝔥 𝔥M Cset ssR ssA = 𝔣 𝔥 , emb𝔣
 where
  emb𝔣 : is-embedding ∣ 𝔣 𝔥 ∣
  emb𝔣 = monic-into-set-is-embedding Cset ∣ 𝔣 𝔥 ∣ (mon𝔣 𝔥 𝔥M ssR ssA)
\end{code}

#### 𝔉 ∈ V(𝒦)

Now, with this result in hand, along with what we proved earlier---namely, PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ V 𝒦---it is not hard to show that 𝔉 belongs to SP(𝒦), and hence to V 𝒦. (Recall, if 𝒦 denotes a class of 𝑆-algebras, then the variety generated 𝒦 is `V 𝒦`, which is equivalent to HSP 𝒦.)

\begin{code}

open class-product-inclusions {𝓤 = 𝓤}{𝒦 = 𝒦}

𝔉∈SP : (𝔥 : ∀ i → X → ∣ 𝔄s i ∣) → (∀ i → Monic (𝔥 i))
       -- truncation assumptions:
 →        is-set ∣ ℭ ∣
 →        (ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q))
          (ssA : ∀ C → is-subsingleton (𝒞{ov 𝓤}{ov 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C))
       --------------------------------------------------------------------
 →     𝔉 ∈ (S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦))

𝔉∈SP 𝔥 𝔥M Cset ssR ssA = ssub (class-prod-s-∈-sp hfe) (𝔉≤ℭ 𝔥 𝔥M Cset ssR ssA)

𝔉∈𝕍 : (𝔥 : ∀ i → X → ∣ 𝔄s i ∣) → (∀ i → Monic (𝔥 i))
       -- truncation assumptions:
 →        is-set ∣ ℭ ∣
 →        (ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q))
          (ssA : ∀ C → is-subsingleton (𝒞{ov 𝓤}{ov 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C))
       --------------------------------------------------------------------
 →     𝔉 ∈ V 𝒦

𝔉∈𝕍 𝔥 𝔥M Cset ssR ssA = SP⊆V' (𝔉∈SP 𝔥 𝔥M Cset ssR ssA)

\end{code}

----------------------------

[← UALib.Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
<span style="float:right;">[UALib.Birkhoff.HSPTheorem →](UALib.Birkhoff.HSPTheorem.html)</span>

{% include UALib.Links.md %}

