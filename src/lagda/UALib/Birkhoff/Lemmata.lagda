---
layout: default
title : UALib.Birkhoff.Lemmata (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

[UALib.Birkhoff ↑](UALib.Birkhoff.html)

### <a id="hsp-lemmas">HSP Lemmas</a>

This section presents the [UALib.Birkhoff.Lemmata][] module of the [Agda Universal Algebra Library][].

Here we establish some facts that will be needed in the proof of Birkhoff's HSP Theorem.  **Warning**: not all of these are very interesting!

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


#### Lemma 0: V is closed under lift

We begin the proof of Birkhoff's HSP theorem by establishing a number of facts that we will eventually string together in the HSPTheorem module to complete the proof.

\begin{code}

open the-free-algebra {𝓤}{𝓤}{X}

module HSPLemmata
 {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 -- extensionality assumptions:
           {hfe : hfunext (OV 𝓤)(OV 𝓤)}
           {pe : propext (OV 𝓤)}
           {ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q)}
           {ssA : ∀ C → is-subsingleton (𝒞{OV 𝓤}{OV 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C)}
 where


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


### Lamma 1: SP(𝒦) ⊆ V(𝒦)

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

### Lemma 2: 𝔽 ≤  ⨅ S(𝒦)

Now we come to a step in the Agda formalization of Birkhoff's theorem that turns out to be surprisingly nontrivial---namely, we need to prove that the relatively free algebra 𝔽 embeds in the product ℭ of all subalgebras of algebras in the given class 𝒦.  To prepare for this, we arm ourselves with a small arsenal of notation.

\begin{code}
 open the-relatively-free-algebra {𝓤 = 𝓤}{𝓧 = 𝓤}{X = X} {𝒦 = 𝒦}
 open class-product {𝓤 = 𝓤}{𝒦 = 𝒦}

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

#### Lemma 3: 𝔽 ≤ ℭ

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

#### Lemma 4: 𝔽 ∈ V(𝒦)

Now, with this result in hand, along with what we proved earlier---namely, PS(𝒦) ⊆ SP(𝒦) ⊆ HSP(𝒦) ≡ 𝕍---it is not hard to show that 𝔽 belongs to SP(𝒦), and hence to 𝕍.

\begin{code}
 open class-product-inclusions {𝓤 = 𝓤}{𝒦 = 𝒦}

 𝔽∈SP : is-set ∣ ℭ ∣ → 𝔽 ∈ (S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦))
 𝔽∈SP Cset = ssub spC (𝔽≤ℭ Cset)
  where
   spC : ℭ ∈ (S{ovu}{ovu} (P{𝓤}{ovu} 𝒦))
   spC = (class-prod-s-∈-sp hfe)

 𝔽∈𝕍 : is-set ∣ ℭ ∣ → 𝔽 ∈ 𝕍
 𝔽∈𝕍 Cset = SP⊆V' (𝔽∈SP Cset)

\end{code}

----------------------------

{% include UALib.Links.md %}

