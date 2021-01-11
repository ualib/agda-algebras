FILE: birkhoff.agda
AUTHOR: William DeMeo
DATE: 30 Jun 2020
UPDATED: 9 Jan 2021

\begin{code}
-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import basic
open import prelude using (global-dfunext; _↪_)

module birkhoff-exp-new-new
 {𝑆 : Signature 𝓞 𝓥}{gfe : global-dfunext}
 {𝕏 : {𝓤 𝓧 : Universe}{X : 𝓧 ̇ }(𝑨 : Algebra 𝓤 𝑆) → X ↠ 𝑨}
 where

open import congruences {𝑆 = 𝑆}{gfe}
open import homomorphisms {𝑆 = 𝑆}{gfe}
open import terms {𝑆 = 𝑆}{gfe}{𝕏} renaming (generator to ℊ)
open import subuniverses {𝑆 = 𝑆}{gfe}{𝕏}
open import closure-exp-new-new {𝑆 = 𝑆}{gfe}{𝕏}

open relation-predicate-classes
open congruence-predicates

--------------------------------------------------------------------------------------------
module the-free-algebra {𝓤 𝓧 : Universe}{X : 𝓧 ̇} where

 -- H (𝑻 X)  (hom images of 𝑻 X)
 𝑻img : Pred (Algebra 𝓤 𝑆) (OV 𝓤) → 𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺ ̇
 𝑻img 𝒦 = Σ 𝑨 ꞉ (Algebra _ 𝑆) , Σ ϕ ꞉ hom (𝑻 X) 𝑨 , (𝑨 ∈ 𝒦) × Epic ∣ ϕ ∣

 -- Every algebra is a hom image of 𝑻 X.
 mkti : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}(𝑨 : Algebra 𝓤 𝑆)
  →     𝑨 ∈ 𝒦 → 𝑻img 𝒦
 mkti 𝑨 KA = (𝑨 , fst thg , KA , snd thg)
  where
   thg : Σ h ꞉ (hom (𝑻 X) 𝑨), Epic ∣ h ∣
   thg = 𝑻hom-gen 𝑨

 -- The algebra part of a hom image of 𝑻 X.
 𝑻𝑨 : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → 𝑻img 𝒦 → Algebra 𝓤 𝑆
 𝑻𝑨 ti = ∣ ti ∣

 -- The hom part of a hom image of 𝑻 X.
 𝑻ϕ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))(ti : 𝑻img 𝒦)
  →   hom (𝑻 X) (𝑻𝑨 ti)
 𝑻ϕ _ ti = fst (snd ti)

 -- The part of a hom image of 𝑻 X that proves the hom is an epi.
 𝑻ϕE : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))(ti : 𝑻img 𝒦)
  →    Epic ∣ 𝑻ϕ 𝒦 ti ∣
 𝑻ϕE _ ti = snd (snd ∥ ti ∥)

 -- The collection of identities (p, q) satisfied by all subalgebras of algebras in 𝒦.
 ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (OV 𝓤)
 ψ  𝒦 (p , q) = ∀(𝑨 : Algebra 𝓤 𝑆) → (sA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦)
                 →  ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti 𝑨 sA) ∣ p ≡ ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦)(mkti 𝑨 sA) ∣ q

 ψRel : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Rel ∣ (𝑻 X) ∣ (OV 𝓤)
 ψRel 𝒦 p q = ψ 𝒦 (p , q)


 ψcompatible : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
  →            compatible (𝑻 X) (ψRel 𝒦)
 ψcompatible 𝒦 f {i} {j} iψj 𝑨 sA = γ
  where
   ti : 𝑻img (S{𝓤}{𝓤} 𝒦)
   ti = mkti 𝑨 sA

   ϕ : hom (𝑻 X) 𝑨
   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) ti

   γ : ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡ ∣ ϕ ∣ ((f ̂ 𝑻 X) j)
   γ = ∣ ϕ ∣ ((f ̂ 𝑻 X) i) ≡⟨ ∥ ϕ ∥ f i ⟩
       (f ̂ 𝑨) (∣ ϕ ∣ ∘ i) ≡⟨ ap (f ̂ 𝑨) (gfe λ x → ((iψj x) 𝑨 sA)) ⟩
       (f ̂ 𝑨) (∣ ϕ ∣ ∘ j) ≡⟨ (∥ ϕ ∥ f j)⁻¹ ⟩
       ∣ ϕ ∣ ((f ̂ 𝑻 X) j) ∎

 ψRefl : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → reflexive (ψRel 𝒦)
 ψRefl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁

 ψSymm : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → symmetric (ψRel 𝒦)
 ψSymm p q pψRelq 𝑪 ϕ = (pψRelq 𝑪 ϕ)⁻¹

 ψTrans : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → transitive (ψRel 𝒦)
 ψTrans p q r pψq qψr 𝑪 ϕ = (pψq 𝑪 ϕ) ∙ (qψr 𝑪 ϕ)

 ψIsEquivalence : {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} → IsEquivalence (ψRel 𝒦)
 ψIsEquivalence = record { rfl = ψRefl ; sym = ψSymm ; trans = ψTrans }

 ψCon : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Congruence (𝑻 X)
 ψCon 𝒦 = mkcon (ψRel 𝒦) (ψcompatible 𝒦) ψIsEquivalence

 -- Properties of ψ ------------------------------------------------------------

 𝑻i⊧ψ : (𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
        (𝑪 : Algebra 𝓤 𝑆)(SCloC : 𝑪 ∈ S{𝓤}{𝓤} 𝒦)
        (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ ψ 𝒦
       --------------------------------------------------
  →     ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦)(mkti 𝑪 SCloC) ∣ p
         ≡ ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦)(mkti 𝑪 SCloC) ∣ q

 𝑻i⊧ψ 𝒦 𝑪 SCloC p q pψq = pψq 𝑪 SCloC

\end{code}

Recall, `mkti X 𝑨 SCloA` has type `𝑻img X (S{𝓤}{𝓤} 𝒦)` and consists of a quadruple:

```agda
(𝑨 , ϕ , SCloA , ϕE),
```

where

```agda
𝑨 : Algebra _ 𝑆 , ϕ : hom (𝑻 X) 𝑨 , SCloA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦 , ϕE : Epic ∣ ϕ ∣
```

Lemma 4.27. (Bergman) Let 𝒦 be a class of algebras, and ψCon defined as above.
                     Then 𝔽 := 𝑻 / ψCon is isomorphic to an algebra in SP(𝒦).
Proof. 𝔽 ↪ ⨅ 𝒜, where 𝒜 = {𝑨 / θ : 𝑨 / θ ∈ S(𝒦)}.
       Therefore, 𝔽 ≅ 𝑩, where 𝑩 is a subalgebra of ⨅ 𝒜 ∈ PS(𝒦).
       Thus 𝔽 is isomorphic to an algebra in SPS(𝒦).
       By SPS⊆SP, 𝔽 is isomorphic to an algebra in SP(𝒦).

### The relatively free algebra

We define it as follows.
\begin{code}


open the-free-algebra

module the-relatively-free-algebra {𝓤 𝓧 : Universe} {X : 𝓧 ̇} {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)} where

 𝓕 : Universe -- (universe level of the relatively free algebra)
 𝓕 = (𝓧 ⊔ (OV 𝓤))⁺

 𝔉 : Algebra 𝓕 𝑆
 𝔉 =  𝑻 X ╱ (ψCon 𝒦)
\end{code}

The domain, ∣ 𝔉 ∣, is defined by

```agda
( ∣ 𝑻 X ∣ /ₚ ⟨ θ ⟩ ) = Σ C ꞉ _ ,  Σ p ꞉ ∣ 𝑻 X ∣ ,  C ≡ ( [ p ] ≈ )
```

which is the collection { C : ∃ p ∈ ∣ 𝑻 X ∣, C ≡ [ p ] } of θ-classs of 𝑻 X.
\begin{code}
 𝔉-free-lift : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
               (h₀ : X → ∣ 𝑨 ∣)  →  ∣ 𝔉 ∣ → ∣ 𝑨 ∣

 𝔉-free-lift {𝓦}𝑨 h₀ (_ , x , _) = (free-lift{𝓧}{𝓦} 𝑨 h₀) x

 𝔉-free-lift-interpretation : (𝑨 : Algebra 𝓤 𝑆)
                              (h₀ : X → ∣ 𝑨 ∣)(𝒙 : ∣ 𝔉 ∣)
                             -------------------------------------
  →                           (⌜ 𝒙 ⌝ ̇ 𝑨) h₀ ≡ 𝔉-free-lift 𝑨 h₀ 𝒙

 𝔉-free-lift-interpretation 𝑨 f 𝒙 = free-lift-interpretation 𝑨 f ⌜ 𝒙 ⌝


 𝔉-lift-hom : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
               (h₀ : X → ∣ 𝑨 ∣) → hom 𝔉 𝑨

 𝔉-lift-hom 𝑨 h₀ = f , fhom
  where
   f : ∣ 𝔉 ∣ → ∣ 𝑨 ∣
   f = 𝔉-free-lift 𝑨 h₀

   ϕ : hom (𝑻 X) 𝑨
   ϕ = lift-hom 𝑨 h₀

   fhom : is-homomorphism 𝔉 𝑨 f
   fhom 𝑓 𝒂 = ∥ ϕ ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝  )

 𝔉-lift-agrees-on-X : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
                       (h₀ : X → ∣ 𝑨 ∣)(x : X)
                     -----------------------------------------
  →                    h₀ x ≡ ( ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ ℊ x ⟧ )

 𝔉-lift-agrees-on-X _ h₀ x = 𝓇ℯ𝒻𝓁

 𝔉-lift-of-epic-is-epic : {𝓦 : Universe}(𝑨 : Algebra 𝓦 𝑆)
                           (h₀ : X → ∣ 𝑨 ∣)  →  Epic h₀
                          --------------------------------
  →                        Epic ∣ 𝔉-lift-hom 𝑨 h₀ ∣

 𝔉-lift-of-epic-is-epic 𝑨 h₀ hE y = γ
  where
   h₀pre : Image h₀ ∋ y
   h₀pre = hE y

   h₀⁻¹y : X
   h₀⁻¹y = Inv h₀ y (hE y)

   η : y ≡ ( ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ ℊ (h₀⁻¹y) ⟧ )
   η = y                               ≡⟨ (InvIsInv h₀ y h₀pre)⁻¹ ⟩
       h₀ h₀⁻¹y                         ≡⟨ (𝔉-lift-agrees-on-X) 𝑨 h₀ h₀⁻¹y ⟩
       ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ⟦ (ℊ h₀⁻¹y) ⟧ ∎

   γ : Image ∣ 𝔉-lift-hom 𝑨 h₀ ∣ ∋ y
   γ = eq y (⟦ ℊ h₀⁻¹y ⟧) η


 𝑻-canonical-projection : (θ : Congruence{OV 𝓧}{𝓤} (𝑻 X)) → epi (𝑻 X) ((𝑻 X) ╱ θ)
 𝑻-canonical-projection θ = canonical-projection (𝑻 X) θ

 𝔉-canonical-projection : epi (𝑻 X) 𝔉
 𝔉-canonical-projection = canonical-projection (𝑻 X) (ψCon 𝒦)

 π𝔉 : hom (𝑻 X) 𝔉
 π𝔉 = epi-to-hom (𝑻 X) {𝔉} 𝔉-canonical-projection

 -- 𝔉-hom-unique : {𝓦 : Universe}{𝑨 : Algebra 𝓦 𝑆}
 --                 (f g : hom 𝔉 𝑨)
 --  →              ((x : X) → ∣ f ∣ ⟦ ℊ x ⟧ ≡ ∣ g ∣ ⟦ ℊ x ⟧)
 --               ---------------------------------------------------
 --  →               ∣ f ∣ ≡ ∣ g ∣
 -- 𝔉-hom-unique f g fxgx = {!!}

 π𝔉-X-defined : (g : hom (𝑻 X) 𝔉)
  →             ((x : X) → ∣ g ∣ (ℊ x) ≡ ⟦ ℊ x ⟧)
  →              (t : ∣ 𝑻 X ∣ )
               ---------------------------------------------------
  →               ∣ g ∣ t ≡ ⟦ t ⟧

 π𝔉-X-defined g gx t = free-unique gfe 𝔉 g π𝔉 gπ𝔉-agree-on-X t
  where
   gπ𝔉-agree-on-X : ((x : X) → ∣ g ∣ (ℊ x) ≡ ∣ π𝔉 ∣ ( ℊ x ))
   gπ𝔉-agree-on-X x = gx x

 X↪𝔉 : X → ∣ 𝔉 ∣
 X↪𝔉 x = ⟦ ℊ x ⟧

 ψlem : (p q : ∣ 𝑻 X ∣ )
  →     ∣ lift-hom 𝔉 X↪𝔉 ∣ p ≡ ∣ lift-hom 𝔉 X↪𝔉 ∣ q
       ----------------------------------------------------------
  →                       (p , q) ∈ ψ 𝒦
 ψlem p q gpgq 𝑨 sA = γ
   where
    g : hom (𝑻 X) 𝔉
    g = lift-hom 𝔉 (X↪𝔉)

    h₀ : X → ∣ 𝑨 ∣
    h₀ = fst (𝕏 𝑨)

    f : hom 𝔉 𝑨
    f = 𝔉-lift-hom 𝑨 h₀

    h ϕ : hom (𝑻 X) 𝑨
    h = HomComp (𝑻 X) 𝑨 g f
    ϕ = 𝑻ϕ (S 𝒦) (mkti 𝑨 sA)

     --(homs from 𝑻 X to 𝑨 that agree on X are equal)
    lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ ℊ x ⟧
    lift-agreement x = 𝔉-lift-agrees-on-X 𝑨 h₀ x
    fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
    fgx≡ϕ x = (lift-agreement x)⁻¹
    h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
    h≡ϕ t = free-unique gfe 𝑨 h ϕ fgx≡ϕ t

    γ : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
    γ = ∣ ϕ ∣ p ≡⟨ (h≡ϕ p)⁻¹ ⟩ (∣ f ∣ ∘ ∣ g ∣) p
               ≡⟨ 𝓇ℯ𝒻𝓁 ⟩ ∣ f ∣ ( ∣ g ∣ p )
               ≡⟨ ap ∣ f ∣ gpgq ⟩ ∣ f ∣ ( ∣ g ∣ q )
               ≡⟨ h≡ϕ q ⟩ ∣ ϕ ∣ q ∎


module proof-of-birkhoff
 {𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
 {X : 𝓤 ̇}
 -- extensionality assumptions:
           {hfe : hfunext (OV 𝓤)(OV 𝓤)}
           {pe : propext (OV 𝓤)}
           {ssR : ∀ p q → is-subsingleton ((ψRel 𝒦) p q)}
           {ssA : ∀ C → is-subsingleton (𝒜{OV 𝓤}{OV 𝓤}{∣ 𝑻 X ∣}{ψRel 𝒦} C)}
 where

 open relation-predicate-classes
 open congruence-predicates
 open class-product-inclusions {𝓤 = 𝓤}{𝒦 = 𝒦}
 open class-product {𝓤 = 𝓤}{𝑆 = 𝑆}{𝒦 = 𝒦}
 -- open birkhoff-relations{𝓤}{𝓤}{X}
 open the-relatively-free-algebra{𝓤}{𝓤}{X}{𝒦}

 -- NOTATION.
 ovu ovu+ ovu++ : Universe
 ovu = 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺
 ovu+ = ovu ⁺
 ovu++ = ovu ⁺ ⁺

 open Lift

 -- Next we prove the lift-alg-V-closure lemma, which helps us deal with annoying universe
 -- level problems. It's a minor techinical issue, but the proof is quite long and tedious.

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


 open Congruence
 --Now we come to what is perhaps the most challenging step in the formalization
 --of Birkhoff's HSP Theorem in Agda---proving that the relatively free algebra 𝔽
 --embeds in the product ℭ of all subalgebras of algebras in 𝒦. For this purpose,
 --we first make some conveninent notations and definitions.

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

 𝔥₀ : X → ∣ ℭ ∣
 𝔥₀ = fst (𝕏 ℭ)          --                             𝔄1
                         --                            /
 ϕ𝔠 : hom (𝑻 X) ℭ        --                           /
 ϕ𝔠 = lift-hom ℭ 𝔥₀      --                          /
                         --        𝑻 -----ϕ≡h--->> ℭ ---𝔄2
 𝔤 : hom (𝑻 X) 𝔽        --         \            77  \
 𝔤 = lift-hom 𝔽 (X↪𝔉)  --          \          /     \
                          --          g        ∃f        𝔄3
 𝔣 : hom 𝔽 ℭ             --            \      /
 𝔣 = 𝔉-free-lift ℭ 𝔥₀ ,   --             \    /     (want: Ψ ⊆ ker h... also want 
     λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝)  --   V l/               ker  ψ = ker g ⊆ ker h => ∃ ϕ: T/ψ → A
                           --            𝔽= 𝑻/ψ     (ker g = Ψ)

 𝔤-⟦⟧ : ∀ p → ∣ 𝔤 ∣ p ≡ ⟦ p ⟧
 𝔤-⟦⟧ p = π𝔉-X-defined 𝔤 (𝔉-lift-agrees-on-X 𝔉 X↪𝔉) p

 --Projection out of the product ℭ onto the specified factor of the product.
 𝔭 : (i : ℑs) → ∣ ℭ ∣ → ∣ 𝔄s i ∣
 𝔭 i 𝒂 = 𝒂 i

 𝔭hom : (i : ℑs) → hom ℭ (𝔄s i)
 𝔭hom = ⨅-projection-hom {I = ℑs}{𝒜 = 𝔄s}

 𝔭𝔣 : ∀ i → ∣ 𝔽 ∣ → ∣ 𝔄s i ∣  -- the composition:
 𝔭𝔣 i = (𝔭 i) ∘ ∣ 𝔣 ∣        --  𝔽  --∣ f𝔣 ∣-->   ℭ   --(pi i)-->   𝔄s i

 𝔭𝔣hom : (i : ℑs) → hom 𝔽 (𝔄s i)
 𝔭𝔣hom i = HomComp 𝔽 (𝔄s i) 𝔣 (𝔭hom i) 


 𝔭ϕ𝔠 : ∀ i → ∣ 𝑻 X ∣ → ∣ 𝔄s i ∣
 𝔭ϕ𝔠 i = ∣ 𝔭hom i ∣ ∘ ∣ ϕ𝔠 ∣

 𝔓 : ∀ i → hom (𝑻 X) (𝔄s i)
 𝔓 i = HomComp (𝑻 X) (𝔄s i) ϕ𝔠 (𝔭hom i)

 𝔭ϕ𝔠≡𝔓 : ∀ i p → (𝔭ϕ𝔠 i) p ≡ ∣ 𝔓 i ∣ p
 𝔭ϕ𝔠≡𝔓 i p = 𝓇ℯ𝒻𝓁

 SP𝒦 : Pred (Algebra (OV 𝓤) 𝑆) (OV (OV 𝓤)) -- SP𝒦 is the class of subalgebras of products of 𝒦.
 SP𝒦 = S{OV 𝓤}{OV 𝓤}(P{𝓤}{OV 𝓤} 𝒦)

 𝔽≤ℭ : is-set ∣ ℭ ∣ → 𝔽 ≤ ℭ
 𝔽≤ℭ Cset = ∣ 𝔣 ∣ , (emb𝔣 , ∥ 𝔣 ∥)
  where
                           --                x ↦ ⟦ ℊ x ⟧
   -- f : hom 𝔽 ℭ
   -- f = 𝔉-lift-hom 𝒦 ℭ h₀
   θ : Rel ∣ 𝑻 X ∣ (OV 𝓤)
   θ = ψRel 𝒦

   mon𝔣 : Monic ∣ 𝔣 ∣
   mon𝔣 (.(θ p) , p , refl _) (.(θ q) , q , refl _) fpq = γ
    where

     pθq : θ p q
     pθq 𝑨 sA = γ'
      where
       𝔭A : hom 𝔽 𝑨
       𝔭A = 𝔭𝔣hom (𝑨 , sA)

       fpq' : ∣ 𝔭A ∣ ⟦ p ⟧ ≡ ∣ 𝔭A ∣ ⟦ q ⟧
       fpq' = ∣ 𝔭A ∣ ⟦ p ⟧ ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
              ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ p ⟧ ) ≡⟨ ap (λ - → (∣ 𝔭hom (𝑨 , sA) ∣ -)) fpq ⟩
              ∣ 𝔭hom (𝑨 , sA) ∣ ( ∣ 𝔣 ∣ ⟦ q ⟧ ) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
              ∣ 𝔭A ∣ ⟦ q ⟧ ∎

       hi : X → ∣ 𝑨 ∣
       hi =  (𝔭 (𝑨 , sA)) ∘ fst(𝕏 ℭ)

       hᵢ₀ : X → ∣ 𝑨 ∣
       hᵢ₀ = fst(𝕏 𝑨)

       f' : hom 𝔽 𝑨
       f' = 𝔉-lift-hom 𝑨 hᵢ₀

       h h' ϕ : hom (𝑻 X) 𝑨
       h = HomComp (𝑻 X) 𝑨 𝔤 f'
       h' = HomComp (𝑻 X) 𝑨 𝔤 𝔭A
       ϕ = 𝑻ϕ (S 𝒦) (mkti 𝑨 sA)

       --(homs from 𝑻 X to 𝑨 that agree on X are equal)
       lift-agreement' : (x : X) → hᵢ₀ x ≡ ∣ f' ∣ ⟦ ℊ x ⟧ -- hᵢ₀
       lift-agreement' x = 𝔉-lift-agrees-on-X 𝑨 hᵢ₀ x -- hᵢ₀

       lift-agreement : (x : X) → hi x ≡ ∣ 𝔭A ∣ ⟦ ℊ x ⟧ -- hᵢ₀
       lift-agreement x = 𝔉-lift-agrees-on-X 𝑨 hi x

       𝔣gx≡ϕ : (x : X) → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
       𝔣gx≡ϕ x = (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) (ℊ x)         ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
                  ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ (ℊ x) )       ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ (ℊ x)) ⟩
                  ∣ 𝔭A ∣ (⟦ ℊ x ⟧)            ≡⟨ (lift-agreement x)⁻¹ ⟩
                   hi x                      ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
                  (𝔭 (𝑨 , sA)) ( ∣ 𝕏 ℭ ∣ x ) ≡⟨ {!!} ⟩
                  ∣ ϕ ∣ (ℊ x) ∎

       f'gx≡ϕ : (x : X) → (∣ f' ∣ ∘ ∣ 𝔤 ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
       f'gx≡ϕ x = (lift-agreement' x)⁻¹

 -- 𝔭𝔣hom : (i : ℑs) → hom 𝔽 (𝔄s i)
 -- 𝔭𝔣hom i = HomComp 𝔽 (𝔄s i) 𝔣 (𝔭hom i)

 -- 𝔥₀ : X → ∣ ℭ ∣
 -- 𝔥₀ = fst (𝕏 ℭ)          --
 -- 𝔣 : hom 𝔽 ℭ             --
 -- 𝔣 = 𝔉-free-lift ℭ 𝔥₀ , λ 𝑓 𝒂 → ∥ ϕ𝔠 ∥ 𝑓 (λ i → ⌜ 𝒂 i ⌝)

       h≡ϕ' : ∀ t → (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) t ≡ ∣ ϕ ∣ t
       h≡ϕ' t = free-unique gfe 𝑨 h' ϕ 𝔣gx≡ϕ t

       SPu : Pred (Algebra 𝓤 𝑆) (OV 𝓤)
       SPu = S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
       i : ℑs
       i = (𝑨 , sA)
       𝔄i : Algebra 𝓤 𝑆
       𝔄i = 𝔄s i
       sp𝔄i : 𝔄i ∈ SPu
       sp𝔄i = S⊆SP{𝓤}{𝓤} sA

       γ' : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
       γ' = ∣ ϕ ∣ p            ≡⟨ (h≡ϕ' p)⁻¹ ⟩
            (∣ 𝔭A ∣ ∘ ∣ 𝔤 ∣) p   ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
            ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ p )   ≡⟨ ap ∣ 𝔭A ∣ (𝔤-⟦⟧ p) ⟩
            ∣ 𝔭A ∣ ⟦ p ⟧        ≡⟨ fpq' ⟩
            ∣ 𝔭A ∣ ⟦ q ⟧        ≡⟨ (ap ∣ 𝔭A ∣ (𝔤-⟦⟧ q))⁻¹ ⟩
            ∣ 𝔭A ∣ ( ∣ 𝔤 ∣ q )   ≡⟨ h≡ϕ' q ⟩
            ∣ ϕ ∣ q            ∎

     γ : ( θ p , p , 𝓇ℯ𝒻𝓁) ≡ ( θ q , q , 𝓇ℯ𝒻𝓁)
     γ = class-extensionality' pe gfe ssR ssA ψIsEquivalence pθq

   emb𝔣 : is-embedding ∣ 𝔣 ∣
   emb𝔣 = monic-into-set-is-embedding Cset ∣ 𝔣 ∣ mon𝔣


 𝔽∈SP : is-set ∣ ℭ ∣ → 𝔽 ∈ (S{ovu}{ovu+} (P{𝓤}{ovu} 𝒦))
 𝔽∈SP Cset = ssub spC (𝔽≤ℭ Cset)
  where
   spC : ℭ ∈ (S{ovu}{ovu} (P{𝓤}{ovu} 𝒦))
   spC = (class-prod-s-∈-sp hfe)

 𝔽∈𝕍 : is-set ∣ ℭ ∣ → 𝔽 ∈ 𝕍
 𝔽∈𝕍 Cset = SP⊆V' (𝔽∈SP Cset)

 -- Birkhoff's theorem: every variety is an equational class.
 birkhoff : is-set ∣ ℭ ∣ → Mod X (Th 𝕍) ⊆ 𝕍

 birkhoff Cset {𝑨} MThVA = γ
  where
   T : Algebra (OV 𝓤) 𝑆
   T = 𝑻 X

   h₀ : X → ∣ 𝑨 ∣
   h₀ = fst (𝕏 𝑨)

   h₀E : Epic h₀
   h₀E = snd (𝕏 𝑨)

   -- We proved 𝔽 ∈ 𝕍 above.
   -- Now we need ϕ : hom 𝔽 𝑨 with ϕE : Epic ∣ ϕ ∣, so we can prove
   -- 𝑨 ∈ 𝕍 by `vhimg (𝔽∈ 𝕍 (𝑨 is-hom-image-of 𝔽)` since the latter
   -- is the constructor of V that yields 𝑨 ∈ 𝕍 𝒦

   ϕ : Σ h ꞉ (hom 𝔽 𝑨) , Epic ∣ h ∣
   ϕ = (𝔉-lift-hom 𝑨 h₀) , 𝔉-lift-of-epic-is-epic 𝑨 h₀ h₀E

   AiF : 𝑨 is-hom-image-of 𝔽
   AiF = (𝑨 , ∣ fst ϕ ∣ , (∥ fst ϕ ∥ , snd ϕ) ) , refl-≅

   γ : 𝑨 ∈ 𝕍
   γ = vhimg (𝔽∈𝕍 Cset) AiF

















-- Lines of code

--  340 prelude.lagda  
--  168 basic.lagda
--  184 congruences.lagda
--  617 homomorphisms.lagda
--  279 terms.lagda
--  600 subuniverses.lagda
-- 1072 closure.lagda
--  740 birkhoff.lagda
-- --------------------
-- TOTAL: 340 + 168 + 184 + 617 + 279 + 600 + 1072 + 740 = 4,000














-- ψ⊆ThSClo : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--  →         ψ X 𝒦 ⊆ (Th (S{𝓤}{𝓤} 𝒦))
-- ψ⊆ThSClo {𝓤} X 𝒦 {p , q} pψq {𝑪} SCloC = γ
--  where
--   ti : 𝑻img X (S{𝓤}{𝓤} 𝒦)
--   ti = mkti X 𝑪 SCloC

--   ϕ : hom (𝑻 X) 𝑪
--   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) ti

--   ϕE : Epic ∣ ϕ ∣
--   ϕE = 𝑻ϕE ti

--   ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
--   ϕsur 𝒄 x = ϕE (𝒄 x)

--   pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 X ∣
--   pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

--   ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
--   ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

-- -- β : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
-- -- β = pψq 𝑪 SCloC

--   β : ∣ ϕ ∣ p ≡ ∣ ϕ ∣ q
--   β = pψq 𝑪 SCloC

--   β' : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
--   β' = {!!} -- ap (λ - → ∣ ϕ ∣ -) (term-agreement p)⁻¹

--   γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
--   γ = gfe λ 𝒄 →
--    (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
--    (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
--    ∣ ϕ ∣ ((p ̇ 𝑻 X)(pre 𝒄))       ≡⟨ intensionality β' (pre 𝒄) ⟩
--    ∣ ϕ ∣ ((q ̇ 𝑻 X)(pre 𝒄))       ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 ϕ q (pre 𝒄) ⟩
--    (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
--    (q ̇ 𝑪) 𝒄                   ∎

-- ψ⊆Th𝒦 : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--          (p q : ∣ (𝑻 X) ∣) → (p , q) ∈ ψ X 𝒦 → 𝒦 ⊧ p ≋ q
-- ψ⊆Th𝒦  X 𝒦 p q pψq {𝑨} KA = ψ⊆ThSClo X 𝒦 {p , q} pψq (sbase KA)





-- 𝔉↪IAS : {𝓤 : Universe} →  hfunext (FU 𝓤) (FU 𝓤)
--  →       {X : 𝓤 ̇}(𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (OV 𝓠))
--          ( 𝑰 : (𝕀{FU 𝓤} (SClo{FU 𝓤} (𝑲 (FU 𝓤)))))
--  →       (𝔉 X (𝑲 𝓤)) IsSubalgebraOf (I→Alg{FU 𝓤}{SClo{FU 𝓤} (𝑲 (FU 𝓤))} 𝑰)
-- 𝔉↪IAS {𝓤} hfe {X} 𝑲 𝑰 = Hmap , (Hemb , Hhom)
--      -- _IsSubalgebraOf_ : {𝓤 𝓠 : Universe}(𝑩 : Algebra 𝓤 𝑆)(𝑨 : Algebra 𝓠 𝑆) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓠 ̇
--      -- 𝑩 IsSubalgebraOf 𝑨 = Σ h ꞉ (∣ 𝑩 ∣ → ∣ 𝑨 ∣) , is-embedding h × is-homomorphism 𝑩 𝑨 h
--  where
--   I : (FU 𝓤) ̇
--   I = ∣ 𝑰 ∣

--   𝒜 : I → Algebra (FU 𝓤) 𝑆
--   𝒜 = fst ∥ 𝑰 ∥

--   𝑨 : Algebra _ 𝑆
--   𝑨 = I→Alg{FU 𝓤}{SClo (𝑲 (FU 𝓤))} 𝑰

--   SClo𝑲 : Pred (Algebra (FU 𝓤) 𝑆) ((FU 𝓤)⁺)
--   SClo𝑲 = (SClo{FU 𝓤}(PClo{FU 𝓤} (𝑲 (FU 𝓤))))

--   SPA : 𝑨 ∈ SClo𝑲
--   SPA = IAS∈SP {𝓤} hfe {𝑲} 𝑰

--   F : Algebra (FU 𝓤) 𝑆
--   F = 𝔉 X (𝑲 𝓤)

--   g : hom (𝑻 X) F
--   g = lift-hom F (X↪𝔉)

--   h₀ : X → ∣ 𝑨 ∣
--   h₀ = fst (𝕏 𝑨)

--   f : hom F 𝑨
--   f = 𝔉-lift-hom X (𝑲 𝓤) 𝑨 h₀

--   h ϕ : hom (𝑻 X) 𝑨
--   h = HCompClosed (𝑻 X) F 𝑨 g f
--   ϕ = 𝑻ϕ SClo𝑲 (mkti X 𝑨 SPA)

--   lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ ℊ x ⟧
--   lift-agreement x = 𝔉-lift-agrees-on-X X (𝑲 𝓤) 𝑨 h₀ x

--   fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
--   fgx≡ϕ x = (lift-agreement x)⁻¹

--   h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
--   h≡ϕ t = free-unique gfe 𝑨 h ϕ fgx≡ϕ t

--   Hmap : ∣ 𝔉 X (𝑲 𝓤) ∣ → ∣ 𝑨 ∣
--   Hmap = ∣ f ∣

--   hom-gen : ∀ i → hom (𝔉 X (𝑲 𝓤)) (𝒜 i)
--   hom-gen i = 𝔉-lift-hom X (𝑲 𝓤) (𝒜 i) ∣ 𝕏 (𝒜 i) ∣

--   pi : (i : I) → ∣ 𝑨 ∣ → ∣ 𝒜 i ∣
--   pi i 𝒂 = 𝒂 i

--   projFA : ∀ i → ∣ 𝔉 X (𝑲 𝓤) ∣ → ∣ 𝒜 i ∣
--   projFA i = (pi i) ∘ Hmap

--   Hemb : is-embedding Hmap
--   Hemb = {!!}

--   Hhom : is-homomorphism (𝔉 X (𝑲 𝓤)) 𝑨 Hmap
--   Hhom = ∥ f ∥


  --    𝑻---- g --->>𝑻/ψ    ψ = ker g ⊆ ker ϕ => ∃ f : T/ψ → A
  --    𝑻---- g --->>𝔽  (ker g = Ψ)
  --     \         .
  --      \       .
  --       ϕ     f     (want: Ψ ⊆ ker h)
  --        \   .
  --         \ .
  --          V
  --          𝑨
-- ⟦_⟧ : {A : 𝓤 ̇} → A → {≈ : Rel A 𝓡} → A // ≈
-- ⟦ a ⟧ {≈} = ([ a ] ≈) , a , 𝓇ℯ𝒻𝓁

  -- ψlem-premise : (p q : ∣ 𝑻 X ∣ ) → Hmap ⟦ p ⟧ ≡ Hmap ⟦ q ⟧
  --  →             (i : I) → (projFA i) ⟦ q ⟧ ≡ (projFA i) ⟦ q ⟧
  -- ψlem-premise p q hyp i = γ
  --  where
  --   γ : projFA i ⟦ p ⟧ ≡ projFA i ⟦ q ⟧
  --   γ = projFA i ⟦ p ⟧ ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
  --       (pi i) ( Hmap ⟦ p ⟧) ≡⟨ ap (pi i) hyp ⟩
  --       (pi i) ( Hmap ⟦ q ⟧) ≡⟨ 𝓇ℯ𝒻𝓁 ⟩
  --       projFA i ⟦ q ⟧ ∎

-- ψlem : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))(p q : ∣ 𝑻 X ∣ )
--  →     ∣ lift-hom (𝔉 X 𝒦) X↪𝔉 ∣ p ≡ ∣ lift-hom (𝔉 X 𝒦) X↪𝔉 ∣ q
--       ----------------------------------------------------------
--  →                       (p , q) ∈ ψ X 𝒦
  -- H1-1 : (p q : ∣ 𝑻 X ∣ ) → Hmap ⟦ p ⟧ ≡ Hmap ⟦ q ⟧ → (p , q) ∈ ψ X (𝑲 𝓤)
  -- H1-1 p q hyp 𝑩 SCloB = ψlem X (𝑲 𝓤) p q η 𝑩 SCloB
  --  where
  --   η : ∣ g ∣ p ≡ ∣ g ∣ q
  --   η = {!!}

-- 𝔉≤IAS : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝑲 : (𝓠 : Universe) → Pred (Algebra 𝓠 𝑆) (OV 𝓠)}
--  →      Σ 𝑰 ꞉ (𝕀{(OV 𝓤)⁺} (SClo (𝑲 ((OV 𝓤)⁺)))) ,
--              (𝔉 X (𝑲 𝓤)) IsSubalgebraOf (I→Alg{(OV 𝓤)⁺}{SClo (𝑲 ((OV 𝓤)⁺))} 𝑰)
-- 𝔉≤IAS = {!!}































-- Ψ : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--  →  Pred (∣ 𝑻 X ∣ × ∣ 𝑻 X ∣) (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)

-- Ψ {𝓤} X 𝒦 (p , q) = ∀(𝑨 : Algebra 𝓤 𝑆) → (SCloA : 𝑨 ∈ S{𝓤}{𝓤} 𝒦)
--  →  ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑨 SCloA) ∣ ∘ (q ̇ 𝑻 X)



-- ΨRel : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)) → Rel ∣ (𝑻 X) ∣ (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)
-- ΨRel X 𝒦 p q = Ψ X 𝒦 (p , q)

-- Ψcompatible : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--  →            compatible{𝓤 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓦 = (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⊔ 𝓧 ⁺)} (𝑻 X)(ΨRel X 𝒦)
-- Ψcompatible{𝓤} X 𝒦 f {𝒕} {𝒔} 𝒕Ψ𝒔 𝑨 SCloA = γ
--  where
--   ϕ : hom (𝑻 X) 𝑨
--   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑨 SCloA)

--   ΨH : ∀ 𝒂 i → (∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻 X)) 𝒂 ≡ (∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻 X))𝒂
--   ΨH 𝒂 i = ap (λ - → - 𝒂)((𝒕Ψ𝒔 i) 𝑨 SCloA)

--   γ : ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒕 i ̇ 𝑻 X)𝒂)) ≡ ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒔 i ̇ 𝑻 X)𝒂))
--   γ =
--     ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒕 i ̇ 𝑻 X) 𝒂))  ≡⟨ i  ⟩
--     (λ 𝒂 → (f ̂ 𝑨)(λ i → ((∣ ϕ ∣ ∘ (𝒕 i ̇ 𝑻 X))𝒂))) ≡⟨ ii ⟩
--     (λ 𝒂 → (f ̂ 𝑨)(λ i → ((∣ ϕ ∣ ∘ (𝒔 i ̇ 𝑻 X))𝒂))) ≡⟨ iii ⟩
--     ∣ ϕ ∣ ∘ (λ 𝒂 → (f ̂ 𝑻 X)(λ i → (𝒔 i ̇ 𝑻 X)𝒂))   ∎
--    where
--     i = gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒕 i ̇ 𝑻 X) 𝒂))
--     ii = gfe (λ 𝒂 → ap (f ̂ 𝑨) (gfe λ i → ΨH 𝒂 i) )
--     iii = (gfe (λ 𝒂 → ∥ ϕ ∥ f (λ i → (𝒔 i ̇ 𝑻 X) 𝒂)))⁻¹

-- ΨSym : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →     symmetric (ΨRel X 𝒦)
-- ΨSym p q pΨRelq 𝑪 ϕ = (pΨRelq 𝑪 ϕ)⁻¹

-- ΨTra : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →     transitive (ΨRel X 𝒦)
-- ΨTra p q r pΨq qΨr 𝑪 ϕ = (pΨq 𝑪 ϕ) ∙ (qΨr 𝑪 ϕ)

-- ΨIsEquivalence : {𝓤 𝓧 : Universe}{X : 𝓧 ̇}{𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤)}
--  →               IsEquivalence (ΨRel X 𝒦)
-- ΨIsEquivalence = record { rfl = λ x 𝑪 ϕ → 𝓇ℯ𝒻𝓁 ; sym = ΨSym ; trans = ΨTra }

-- ΨCon : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--  →     Congruence{𝓠 = (𝓞 ⊔ 𝓥 ⊔ 𝓧 ⁺)}{𝓤 = (𝓞 ⊔ 𝓥 ⊔ (𝓤 ⊔ 𝓧)⁺)} (𝑻 X)
-- ΨCon X 𝒦 = mkcon (ΨRel X 𝒦) (Ψcompatible X 𝒦) ΨIsEquivalence


-- -- Properties of Ψ ------------------------------------------------------------

-- 𝑻i⊧Ψ : {𝓤 𝓧 : Universe}
--        (X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--        (𝑪 : Algebra 𝓤 𝑆)(SCloC : 𝑪 ∈ S{𝓤}{𝓤} 𝒦)
--        (p q : ∣ (𝑻 X) ∣)  →  (p , q) ∈ Ψ X 𝒦
--       --------------------------------------------------
--  →     ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑪 SCloC) ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑪 SCloC) ∣ ∘ (q ̇ 𝑻 X)

-- 𝑻i⊧Ψ{𝓤} X 𝒦 𝑪 SCloC p q pΨq = pCq
--  where

--   ϕ : hom (𝑻 X) 𝑪
--   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) (mkti X 𝑪 SCloC)

--   pCq : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
--   pCq = pΨq 𝑪 SCloC


-- Ψ⊆ThSClo : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--  →         Ψ X 𝒦 ⊆ (Th (S{𝓤}{𝓤} 𝒦))
-- Ψ⊆ThSClo{𝓤} X 𝒦 {p , q} pΨq {𝑪} SCloC = γ
--  where
--   ti : 𝑻img X (S{𝓤}{𝓤} 𝒦)
--   ti = mkti X 𝑪 SCloC

--   ϕ : hom (𝑻 X) 𝑪
--   ϕ = 𝑻ϕ (S{𝓤}{𝓤} 𝒦) ti

--   ϕE : Epic ∣ ϕ ∣
--   ϕE = 𝑻ϕE ti

--   ϕsur : (𝒄 : X → ∣ 𝑪 ∣ )(x : X) → Image ∣ ϕ ∣ ∋ (𝒄 x)
--   ϕsur 𝒄 x = ϕE (𝒄 x)

--   pre : (𝒄 : X → ∣ 𝑪 ∣)(x : X) → ∣ 𝑻 X ∣
--   pre 𝒄 x = (Inv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x))

--   ζ : (𝒄 : X → ∣ 𝑪 ∣) → ∣ ϕ ∣ ∘ (pre 𝒄) ≡ 𝒄
--   ζ 𝒄 = gfe λ x → InvIsInv ∣ ϕ ∣ (𝒄 x) (ϕsur 𝒄 x)

--   β : ∣ ϕ ∣ ∘ (p ̇ 𝑻 X) ≡ ∣ ϕ ∣ ∘ (q ̇ 𝑻 X)
--   β = pΨq 𝑪 SCloC

--   γ : (p ̇ 𝑪) ≡ (q ̇ 𝑪)
--   γ = gfe λ 𝒄 →
--    (p ̇ 𝑪) 𝒄                  ≡⟨ (ap (p ̇ 𝑪) (ζ 𝒄))⁻¹ ⟩
--    (p ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ (comm-hom-term gfe (𝑻 X) 𝑪 ϕ p (pre 𝒄))⁻¹ ⟩
--    ∣ ϕ ∣ ((p ̇ 𝑻 X)(pre 𝒄))       ≡⟨ intensionality β (pre 𝒄) ⟩
--    ∣ ϕ ∣ ((q ̇ 𝑻 X)(pre 𝒄))       ≡⟨ comm-hom-term gfe (𝑻 X) 𝑪 ϕ q (pre 𝒄) ⟩
--    (q ̇ 𝑪)(∣ ϕ ∣ ∘ (pre 𝒄))     ≡⟨ ap (q ̇ 𝑪) (ζ 𝒄) ⟩
--    (q ̇ 𝑪) 𝒄                   ∎

-- Ψ⊆Th𝒦 : {𝓤 𝓧 : Universe}(X : 𝓧 ̇)(𝒦 : Pred (Algebra 𝓤 𝑆) (OV 𝓤))
--          (p q : ∣ (𝑻 X) ∣) → (p , q) ∈ Ψ X 𝒦 → 𝒦 ⊧ p ≋ q
-- Ψ⊆Th𝒦{𝓤}  X 𝒦 p q pΨq {𝑨} KA = γ
--  where
--   ξ : (S 𝒦) ⊧ p ≋ q
--   ξ = Ψ⊆ThSClo X 𝒦 {p , q} pΨq

--   lApq : (lift-alg 𝑨 𝓤) ⊧ p ≈ q
--   lApq = ξ (sbase KA)

--   γ : 𝑨 ⊧ p ≈ q
--   γ = lower-alg-⊧ 𝑨 p q lApq






























--     where
--      SPC : ℭ ∈ SP𝒦
--      SPC = class-prod-s-∈-sp hfe

--      g : hom (𝑻 X) 𝔽
--      g = lift-hom 𝔽 (X↪𝔉)

--      h ϕ : hom (𝑻 X) ℭ
--      h = HCompClosed (𝑻 X) 𝔽 ℭ g f
--      ϕ = lift-hom ℭ h₀ -- 𝑻ϕ SP𝒦 (mkti ℭ SPC)

--      lift-agreement : (x : X) → h₀ x ≡ ∣ f ∣ ⟦ ℊ x ⟧
--      lift-agreement x = 𝔉-lift-agrees-on-X 𝒦 ℭ h₀ x

--      fgx≡ϕ : (x : X) → (∣ f ∣ ∘ ∣ g ∣) (ℊ x) ≡ ∣ ϕ ∣ (ℊ x)
--      fgx≡ϕ x = (lift-agreement x)⁻¹

--      h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
--      h≡ϕ t = free-unique gfe ℭ h ϕ fgx≡ϕ t

--      kerg : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ 𝔽 ∣} ∣ g ∣) ⊆ ψ 𝒦
--      kerg {p , q} gpq = ψlem p q gpq

--      -- kerh⊆kerg : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ ℭ ∣} ∣ h ∣) ⊆ (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ 𝔉 X 𝒦 ∣} ∣ g ∣)
--      -- kerh⊆kerg {p , q} hpq = {!!}

--      pi : (i : ℑs) → ∣ ℭ ∣ → ∣ 𝔄s i ∣
--      pi i 𝒂 = 𝒂 i

--      pihom : (i : ℑs) → hom ℭ (𝔄s i)
--      pihom = ⨅-projection-hom {I = ℑs}{𝒜 = 𝔄s}

--      projFA : ∀ i → ∣ 𝔽 ∣ → ∣ 𝔄s i ∣  -- 𝔽 →  ℭ  → (𝔄s i)
--      projFA i = (pi i) ∘ ∣ f ∣

--      piϕ : ∀ i → ∣ 𝑻 X ∣ → ∣ 𝔄s i ∣
--      piϕ i = ∣ pihom i ∣ ∘ ∣ ϕ ∣

--      Phi : ∀ i → hom (𝑻 X) (𝔄s i)
--      Phi i = HomComp (𝑻 X) (𝔄s i) ϕ (pihom i)

--      piϕ≡Phi : ∀ i p → (piϕ i) p ≡ ∣ Phi i ∣ p
--      piϕ≡Phi i p = 𝓇ℯ𝒻𝓁

--      -- kerf : (KER-pred{A = ∣ 𝔽 ∣}{B = ∣ ℭ ∣} ∣ f ∣) ⊆ ψ 𝒦
--      -- kerf {p , q} fpq = ?

--      kerϕ : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ ℭ ∣} ∣ ϕ ∣) ⊆ ψ 𝒦
--      kerϕ {p , q} ϕpq 𝑨 sA = γ
--       where
--        SPu : Pred (Algebra 𝓤 𝑆) (OV 𝓤)
--        SPu = S{𝓤}{𝓤} (P{𝓤}{𝓤} 𝒦)
--        i : ℑs
--        i = (𝑨 , sA)
--        𝔄i : Algebra 𝓤 𝑆
--        𝔄i = 𝔄s i
--        sp𝔄i : 𝔄i ∈ SPu
--        sp𝔄i = S⊆SP{𝓤}{𝓤} sA

--        α₀ β₀ : X → ∣ 𝔄i ∣
--        α₀ = fst (𝕏 𝔄i)
--        β₀ = (pi i) ∘ h₀

--        α β : hom (𝑻 X) 𝔄i
--        α = lift-hom 𝔄i α₀
--        β = lift-hom 𝔄i β₀

--        Phii : hom (𝑻 X) 𝔄i
--        Phii = (Phi i)

--        lift-agree : (x : X) → ∣ β ∣ (ℊ x) ≡ ∣ pihom i ∣ ( ∣ ϕ ∣ (ℊ x))
--        lift-agree x = 𝓇ℯ𝒻𝓁

--        lift-agree' : (x : X) → ∣ α ∣ (ℊ x) ≡ ∣ β ∣ ( ℊ x)
--        lift-agree' x = {!!}

--        ϕpqi : (i : ℑs) → (∣ ϕ ∣ p) i ≡  ∣ ϕ ∣ q i
--        ϕpqi i = ap (λ - → - i) ϕpq

--        frl : ∣ ϕ ∣ p ≡ (p ̇ ℭ) (fst (𝕏 ℭ))
--        frl = (free-lift-interpretation ℭ (fst (𝕏 ℭ)) p)⁻¹

--        -- h≡ϕ : ∀ t → (∣ f ∣ ∘ ∣ g ∣) t ≡ ∣ ϕ ∣ t
--        -- h≡ϕ t = free-unique gfe ℭ h ϕ fgx≡ϕ t
--        piϕ-α-agree : ∀ p → (∣ Phi i ∣) p ≡ ∣ α ∣ p
--        piϕ-α-agree p = {!!}

--        γ : ∣ α ∣ p ≡ ∣ α ∣ q
--        γ = ∣ α ∣ p     ≡⟨ (piϕ-α-agree p)⁻¹  ⟩
--            (∣ ϕ ∣ p) i ≡⟨ ϕpqi i ⟩
--            (∣ ϕ ∣ q) i ≡⟨ piϕ-α-agree q ⟩
--            ∣ α ∣ q     ∎

-- -- ϕ : ∣ 𝑻 X ∣ → ∣ ℭ ∣
-- -- ϕ = ∣ 𝑻ϕ SP𝒦 (mkti ℭ SPC) ∣
-- -- This is constructed as follows:
-- --  1. start with a map from X to ∣ ℭ ∣ (which is always available by 𝕏)
-- --
-- --     ϕ₀ : X → ∣ ℭ ∣
-- --     ϕ₀ = fst (𝕏 ℭ)
-- --
-- --  2. Then use lift-hom to get ϕ : hom (𝑻 X) ℭ
-- --
-- --     ϕ : hom (𝑻 X) ℭ
-- --     ϕ = lift-hom ℭ h₀
-- --

-- -- pi ∘ h₀ : X → ∣ ℭ ∣ → ∣ 𝔄 i ∣

--      --Want kerf ⊆ ψ 𝒦, as this should enable us to prove that f is an embedding.
--      --We have h = f ∘ g and kerg ≡ ψ 𝒦 we want ker h ⊆ ψ 𝒦
--      -- pϕ : ∀ i → ∣ 𝑻 X ∣ → ∣ 𝔄s i ∣
--      -- pϕ i = (pi i) ∘ ϕ

--      -- kerϕ : (KER-pred{A = ∣ 𝑻 X ∣}{B = ∣ ℭ ∣} ∣ ϕ ∣) ⊆ ψ X 𝒦
--      -- kerϕ {p , q} ϕpq = λ 𝑨 SCloA →
--      --  ∣ 𝑻ϕ (S 𝒦) (mkti X 𝑨 SCloA) ∣ p ≡⟨ ? ⟩
--       -- ∣ pϕ ∣ p  ≡⟨ ? ⟩ ∣ ϕ ∣ q   ≡⟨ ? ⟩  ∣ 𝑻ϕ (S 𝒦) (mkti X 𝑨 SCloA) ∣ q ∎

-- -- KER-pred : {𝓤 𝓦 : Universe}{A : 𝓤 ̇}{B : 𝓦 ̇} → (A → B) → Pred (A × A) 𝓦
-- -- KER-pred g (x , y) = g x ≡ g y


--      hom-gen : ∀ i → hom 𝔽(𝔄s i)
--      hom-gen i = 𝔉-lift-hom 𝒦 (𝔄s i) ∣ 𝕏 (𝔄s i) ∣

--      -- h : hom T 𝑨
--      -- h = lift-hom 𝑨 h₀
--      -- hE : Epic ∣ h ∣
--      -- hE = lift-of-epi-is-epi 𝑨 h₀ h₀E

--      -- g₀ : X → ∣ 𝔽 ∣
--      -- g₀ = fst (𝕏 𝔽)

--      -- g₀E : Epic g₀
--      -- g₀E = snd (𝕏 𝔽)

--      -- gg : Σ g ꞉ hom T 𝔽 , Epic ∣ g ∣
--      -- gg = (lift-hom 𝔽 g₀) , (lift-of-epi-is-epi{𝓤}{(OV 𝓤)⁺} 𝔽 g₀ g₀E)

--      -- g' : hom (𝑻 X)(𝔉 X 𝒦)
--      -- g' = lift-hom (𝔉 X 𝒦) X↪𝔉

--      -- g : hom T 𝔽
--      -- g = fst gg

--      -- gE : Epic ∣ g ∣
--      -- gE = snd gg

--      -- τ : (𝑨 : Algebra ovu+ 𝑆)(SCloA : S{𝓤}{ovu+} 𝒦 𝑨) → hom (𝑻 X) 𝑨
--      -- τ 𝑨 SCloA = 𝑻ϕ (S{𝓤}{ovu+} 𝒦) (mkti X 𝑨 SCloA)

--      γ : is-embedding ∣ f ∣
--      γ = {!!}

--    -- kerg⊆kerh : KER-pred ∣ g' ∣ ⊆ KER-pred ∣ h ∣
--    -- kerg⊆kerh {x , y} gx≡gy = ψ⊆Kerh {x , y}(kerg{x , y} gx≡gy)

--    -- N.B. Ψ is the kernel of 𝑻 → 𝔽(𝒦, 𝑻).  Therefore, to prove 𝑨 is a homomorphic image of 𝔽(𝒦, 𝑻),
--    -- it suffices to show that the kernel of h : 𝑻 → 𝑨 contains Ψ.
--    --
--    --    𝑻---- g --->>𝑻/ψ    ψ = ker g ⊆ ker h => ∃ ϕ: T/ψ → A
--    --    𝑻---- g --->>𝔽  (ker g = Ψ)
--    --     \         .
--    --      \       .
--    --      ϕ≡h    ∃f     (want: Ψ ⊆ ker h... also want ker
--    --        \   .
--    --         \ .
--    --          V
--    --          ℭ












-       
