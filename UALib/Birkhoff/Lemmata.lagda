---
layout: default
title : UALib.Birkhoff.Lemmata (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="hsp-lemmas">HSP Lemmas</a>

This section presents the [UALib.Birkhoff.Lemmata][] module of the [Agda Universal Algebra Library][].

Here we establish some facts that will be needed in the proof of Birkhoff's HSP Theorem.
**Warning**: not all of these are very interesting!

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UALib.Algebras using (Signature; 𝓞; 𝓥; Algebra; _↠_)
open import UALib.Prelude.Preliminaries using (global-dfunext; Universe; _̇)


module UALib.Birkhoff.Lemmata
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 {𝓤 : Universe} {X : 𝓤 ̇}
 where


open import UALib.Birkhoff.FreeAlgebra {𝑆 = 𝑆}{gfe}{𝕏} public

\end{code}


#### Lemma 1: V is closed under lift

We begin the proof of Birkhoff's HSP theorem by establishing a number of facts that we will eventually string together in the HSPTheorem module to complete the proof.

\begin{code}

open the-free-algebra {𝓤}{𝓤}{X}

module HSPLemmata
 {𝒦 : Pred (Algebra 𝓤 𝑆) (ov 𝓤)}
    -- extensionality assumptions:
    {hfe : hfunext (ov 𝓤)(ov 𝓤)}
    {pe : propext (ov 𝓤)}
    -- truncation assumptions:
    {ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q)}
    {ssA : ∀ C → is-subsingleton (𝒞{ov 𝓤}{ov 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C)}
 where

 -- NOTATION.
 ovu ovu+ : Universe
 ovu = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
 ovu+ = ovu ⁺

\end{code}

We prove the `lift-alg-V-closure` lemma, which says that if an algebra 𝑨 belongs to the variety 𝕍, then so does its lift.  This dispenses with annoying universe level problems that arise later---a minor techinical issue with an uninteresting proof.

\begin{code}

 open Lift
 lift-alg-V-closure -- (alias)
  VlA : {𝑨 : Algebra ovu 𝑆}
   →     𝑨 ∈ V{𝓤}{ovu} 𝒦
       ---------------------------------
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

### Lamma 2: SP(𝒦) ⊆ V(𝒦)

In the [UALib.Varieties.Varieties][] module, we proved that `SP(𝒦) ⊆ V(𝒦)` holds with fairly general universe level parameters.  Unfortunately, this was not general enough for our purposes, so we prove the inclusion again for the specific universe parameters that align with subsequent applications of this result.

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

### Lemma 3: 𝔉 ≤  ⨅ S(𝒦)  (=: ℭ)

Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial. We must prove that the free algebra 𝔉 embeds in the product ℭ of all subalgebras of algebras in the class 𝒦.  This is the only stage in the proof of Birkhoff's theorem that requires the truncation assumption that ℭ be a set. To prepare for the proof, we arm ourselves with a small arsenal of notation.

\begin{code}
 open the-relatively-free-algebra {𝓤 = 𝓤}{𝓧 = 𝓤}{X = X} {𝒦 = 𝒦}
 open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}

 -- NOTATION.
 -- 𝕍 is HSP(𝒦)
 𝕍 : Pred (Algebra ovu+ 𝑆) (ovu+ ⁺)
 𝕍 = V{𝓤}{ovu+} 𝒦

 ℑs : ovu ̇
 ℑs = ℑ (S{𝓤}{𝓤} 𝒦)

 𝔄s : ℑs → Algebra 𝓤 𝑆
 𝔄s = λ (i : ℑs) → ∣ i ∣

 SK𝔄 : (i : ℑs) → (𝔄s i) ∈ S{𝓤}{𝓤} 𝒦
 SK𝔄 = λ (i : ℑs) → ∥ i ∥

 -- ℭ is the product of all subalgebras of algebras in 𝒦.
 ℭ : Algebra ovu 𝑆
 ℭ = ⨅ 𝔄s
 -- Elements of ℭ are mappings from ℑs to {𝔄s i : i ∈ ℑs}

 𝔥₀ : X → ∣ ℭ ∣
 𝔥₀ x = λ i → (fst (𝕏 (𝔄s i))) x

 ϕ𝔠 : hom (𝑻 X) ℭ
 ϕ𝔠 = lift-hom ℭ 𝔥₀

 𝔤 : hom (𝑻 X) 𝔉
 𝔤 = lift-hom 𝔉 (X↪𝔉)

 𝔣 : hom 𝔉 ℭ
 𝔣 = 𝔉-free-lift ℭ 𝔥₀ , λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝)

 𝔤-⟦⟧ : ∀ p → ∣ 𝔤 ∣ p ≡ ⟦ p ⟧
 𝔤-⟦⟧ p = π𝔉-X-defined 𝔤 (𝔉-lift-agrees-on-X 𝔉 X↪𝔉) p

 -- 𝔭 i is the projection out of the product ℭ onto the i-th factor.
 𝔭 : (i : ℑs) → ∣ ℭ ∣ → ∣ 𝔄s i ∣
 𝔭 i 𝒂 = 𝒂 i

 𝔭hom : (i : ℑs) → hom ℭ (𝔄s i)
 𝔭hom = ⨅-projection-hom {I = ℑs}{𝒜 = 𝔄s}

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

 -- 𝔭𝔣 is the composition:  𝔉 -- 𝔣 -->  ℭ -- 𝔭 i --> 𝔄s i
 𝔭𝔣 : ∀ i → ∣ 𝔉 ∣ → ∣ 𝔄s i ∣
 𝔭𝔣 i = (𝔭 i) ∘ ∣ 𝔣 ∣

 𝔭𝔣hom : (i : ℑs) → hom 𝔉 (𝔄s i)
 𝔭𝔣hom i = HomComp 𝔉 (𝔄s i) 𝔣 (𝔭hom i)

\end{code}

Armed with these tools, we proceed to the proof that the free algebra 𝔉 is a subalgebra of the product ℭ of all subalgebras of algebras in 𝒦.  The hard part of the proof is showing that `𝔣 : hom 𝔉 ℭ` is a monomorphism. Let's dispense with that first.

\begin{code}
 Ψ : Rel ∣ 𝑻 X ∣ (ov 𝓤)
 Ψ = ψRel 𝒦

 mon𝔣 : Monic ∣ 𝔣 ∣
 mon𝔣 (.(Ψ p) , p , refl _) (.(Ψ q) , q , refl _) fpq = γ
  where

   pΨq : Ψ p q
   pΨq 𝑨 sA = γ'
    where
     𝔭A : hom 𝔉 𝑨
     𝔭A = 𝔭𝔣hom (𝑨 , sA)

     𝔣pq : ∣ 𝔭A ∣ ⟦ p ⟧ ≡ ∣ 𝔭A ∣ ⟦ q ⟧
     𝔣pq = ∣ 𝔭A ∣ ⟦ p ⟧                    ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ p ⟧ ) ≡⟨ ap (λ - → (∣ 𝔭hom (𝑨 , sA) ∣ -)) fpq ⟩
          ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ q ⟧ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
          ∣ 𝔭A ∣ ⟦ q ⟧                     ∎

     h ϕ : hom (𝑻 X) 𝑨
     h = HomComp (𝑻 X) 𝑨 𝔤 𝔭A
     ϕ = lift-hom 𝑨 ((𝔭 (𝑨 , sA)) ∘ 𝔥₀)

     𝔣gx≡ϕ : (x : X) → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
     𝔣gx≡ϕ x = ∣ 𝔭A ∣ (∣ 𝔤 ∣ (ℊ x)) ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ (ℊ x)) ⟩
               ∣ 𝔭A ∣ (⟦ ℊ x ⟧)   ≡⟨(𝔉-lift-agrees-on-X 𝑨 ((𝔭 (𝑨 , sA)) ∘ 𝔥₀) x)⁻¹ ⟩
               ∣ ϕ ∣ (ℊ x)        ∎

     h≡ϕ' : ∀ t → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) t ≡ ∣ ϕ ∣ t
     h≡ϕ' t = free-unique gfe 𝑨 h ϕ 𝔣gx≡ϕ t

     γ' : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
     γ' = ∣ ϕ ∣ p            ≡⟨ (h≡ϕ' p)⁻¹ ⟩
          ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ p ) ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ p) ⟩
          ∣ 𝔭A ∣ ⟦ p ⟧       ≡⟨ 𝔣pq ⟩
          ∣ 𝔭A ∣ ⟦ q ⟧       ≡⟨ (ap ∣ 𝔭A ∣ (𝔤-⟦⟧ q))⁻¹ ⟩
          ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ q ) ≡⟨ h≡ϕ' q ⟩
          ∣ ϕ ∣ q            ∎

   γ : ( Ψ p , p , 𝓇ℯ𝒻𝓁) ≡ ( Ψ q , q , 𝓇ℯ𝒻𝓁)
   γ = class-extensionality' pe gfe ssR ssA ψIsEquivalence pΨq

\end{code}

With that out of the way, the proof that 𝔉 is (isomorphic to) a subalgebra of ℭ is all but complete.

\begin{code}
 𝔉≤ℭ : is-set ∣ ℭ ∣ → 𝔉 ≤ ℭ
 𝔉≤ℭ Cset = ∣ 𝔣 ∣ , (emb𝔣 , ∥ 𝔣 ∥)
  where
   emb𝔣 : is-embedding ∣ 𝔣 ∣
   emb𝔣 = monic-into-set-is-embedding Cset ∣ 𝔣 ∣ mon𝔣
\end{code}

#### Lemma 4: 𝔉 ∈ V(𝒦)

Now, with this result in hand, along with what we proved earlier---namely, PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ 𝕍---it is not hard to show that 𝔉 belongs to SP(𝒦), and hence to 𝕍.

\begin{code}
 open class-product-inclusions {𝓤 = 𝓤}{𝒦 = 𝒦}

 𝔉∈SP : is-set ∣ ℭ ∣ → 𝔉 ∈ (S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦))
 𝔉∈SP Cset = ssub spC (𝔉≤ℭ Cset)
  where
   spC : ℭ ∈ (S{ovu}{ovu} (P{𝓤}{ovu} 𝒦))
   spC = (class-prod-s-∈-sp hfe)

 𝔉∈𝕍 : is-set ∣ ℭ ∣ → 𝔉 ∈ 𝕍
 𝔉∈𝕍 Cset = SP⊆V' (𝔉∈SP Cset)

\end{code}

----------------------------

[← UALib.Birkhoff.FreeAlgebra](UALib.Birkhoff.FreeAlgebra.html)
<span style="float:right;">[UALib.Birkhoff.Theorem →](UALib.Birkhoff.Theorem.html)</span>

{% include UALib.Links.md %}

