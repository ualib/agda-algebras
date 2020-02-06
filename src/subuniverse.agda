--File: subuniverse.agda
--Author: William DeMeo
--Date: 10 Jan 2020
--Updated: 6 Feb 2020

{-# OPTIONS --without-K --exact-split #-}

open import Level

open import basic
open algebra
open signature

module subuniverse {ℓ : Level} {S : signature} where

open import preliminaries

open import Data.Empty
open import Data.Unit.Base using (⊤)
open import Data.Product
open import Data.Sum using (_⊎_; [_,_])
open import Function
open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

OpClosed : (A : algebra S) (B : Pred ⟦ A ⟧ᵤ ℓ) -> Set ℓ
OpClosed A B = ∀{𝓸 : ⟨ S ⟩ₒ}
               (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ) 
  ->           ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ B
              -------------------------------------------
  ->           (A ⟦ 𝓸 ⟧) args ∈ B

record IsSubuniverse {A : algebra S} : Set (suc ℓ) where

  field
    sset : Pred ⟦ A ⟧ᵤ ℓ
    closed : OpClosed A sset    


--subalgebra type
record subalgebra (A : algebra S) : Set (suc ℓ) where

  field

    subuniv : Pred ⟦ A ⟧ᵤ ℓ
    _⟦_⟧ : (𝓸 : ⟨ S ⟩ₒ)
      ->   (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ)
      ->   ( ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ subuniv )
         --------------------------------------------------
      ->   Set ℓ
      
    closed : OpClosed A subuniv



open IsSubuniverse

SubAlgebra : (A : algebra S)
  ->         (B : IsSubuniverse {A})
           --------------------------
  ->         (subalgebra A)

SubAlgebra A B =
  record
    {
    subuniv = sset B ;
    _⟦_⟧ = λ 𝓸 args p -> (sset B) ((A ⟦ 𝓸 ⟧) args) ;
    closed = closed B
    }

-- Recall, Theorem 4.32 of Bergman.
-- Let A and B be algebras of type S. Then the following hold:
--
--   (1) For every n-ary term t and homomorphism g: A —> B, 
--       g(tᴬ(a₁,...,aₙ)) = tᴮ(g(a₁),...,g(aₙ)).
--   (2) For every term t ∈ T(X) and every θ ∈ Con(A), 
--       a θ b => t(a) θ t(b).
--   (3) For every subset Y of A,
--       Sg(Y) = { t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, and aᵢ ∈ Y, for i ≤ n}.
--
-- (1) is proved in free.agda (see: comm-hom-term)
-- (2) is proved in free.agda (see: compatible-term and Compatible-Term)
--
-- PROOF of (3).
--
-- (3) For every subset Y of A,
--     Sg(Y) = { t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, and aᵢ ∈ Y, for i ≤ n}.
--
-- _⊆_ : ∀ {ℓ₃ ℓ ℓ₂} {Σ : signature} {A : Algebra {ℓ} {ℓ₂} Σ} →
--         Congruence {ℓ₃} A → Congruence {ℓ₃} A → Set _
-- Φ ⊆ Ψ = ∀ s → (rel Φ s) ⇒ (rel Ψ s)


--     -- subuniverse ------------------------------------------------
--     def Sub {𝔸: algebra σ} (B₀: set 𝔸): Prop:=
--     ∀ (f: β) (a: ρ f → 𝔸), (∀ x, a x ∈ B₀) → (𝔸.snd f a) ∈ B₀
--        -- (N.B. 𝔸 f a ∈ B₀  is syntactic sugar for  B₀ (𝔸 f a).)

--     -- is subalgebra? ---------------------------------------------
--     def is_subalgebra (𝔸: algebra σ) 
--     (B₀: set 𝔸) (𝔹: algebra_on σ B₀): Prop:= 
--     ∀ f b, ↑(𝔹 f b) = 𝔸.snd f ↑b

--     -- subuniverse generated by X ---------------------------------
--     def Sg {𝔸: algebra σ} (X: set 𝔸): set 𝔸:= 
--     ⋂₀ {U | Sub U ∧ X ⊆ U}

--     -- intersection introduction ----------------------------------
--     theorem Inter.intro {𝔸: algebra σ} {x: 𝔸} {s: γ → set 𝔸}: 
--     (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
--     assume h, iff.elim_right set.mem_Inter h

--     -- intersection elimination -------------------------------------
--     theorem Inter.elim {𝔸: algebra σ} {x: 𝔸} {C: γ → set 𝔸}: 
--     (x ∈ ⋂ i, C i) →  (∀ i, x ∈ C i):= 
--     assume h, iff.elim_left set.mem_Inter h
    
--     -- Intersection of subuniverses is a subuniverse ---------------
--     lemma sub_of_sub_inter_sub {𝔸: algebra σ} (C: γ → set 𝔸): 
--     (∀ i, Sub (C i)) → Sub (⋂i, C i):= 
--     assume h: (∀ i, Sub (C i)), show Sub (⋂i, C i), from
--     assume (f: β) (a: ρ f → 𝔸) (h₁: ∀ x, a x ∈ ⋂i, C i),
--     show 𝔸.snd f a ∈ ⋂i, C i, from 
--       Inter.intro                -- x = (𝔸 f a)
--       (λ j, (h j) f a (λ x, Inter.elim (h₁ x) j))

--     -- X is a subset of Sgᴬ(X) ----------------------------------------
--     lemma subset_X_of_SgX {𝔸: algebra σ} (X : set 𝔸): X ⊆ Sg X:= 
--     assume x (h: x ∈ X), 
--       show x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from 
--         assume W (h₁: W ∈ {U | Sub U ∧ X ⊆ U}),  
--         show x ∈ W, from 
--           have h₂: Sub W ∧ X ⊆ W, from h₁, 
--         h₂.right h

--     -- A subuniverse that contains X also contains Sgᴬ X ------------------------
--     lemma sInter_mem {𝔸: algebra σ} {X: set 𝔸}:
--     ∀ R, Sub R → X ⊆ R → (Sg X ⊆ R) := 
--     assume R (h₁: Sub R) (h₂: X ⊆ R),
--     show Sg X ⊆ R, from 
--       assume x (h: x ∈ Sg X), show x ∈ R, from 
--         h R (and.intro h₁ h₂)

--     lemma sInter_mem' {𝔸: algebra σ} {X: set 𝔸}:
--     ∀ R, Sub R ∧ X ⊆ R → (Sg X ⊆ R):= 
--     assume R (hc : Sub R ∧ X ⊆ R),
--     have h₁: Sub R, from hc.left,
--     have h₂: X ⊆ R, from hc.right,
--     show Sg X ⊆ R, from 
--       assume x (h: x ∈ Sg X), show x ∈ R, from 
--         h R (and.intro h₁ h₂)

--     lemma sInter_mem'' {𝔸: algebra σ} {X: set 𝔸}:
--     ∀ x, x ∈ Sg X → ∀ R, Sub R → X ⊆ R → x ∈ R:= 
--     assume x (h₁: x ∈ Sg X) (R: set 𝔸) (h₂: Sub R) (h₃: X ⊆ R), 
--     show x ∈ R, from h₁ R (and.intro h₂ h₃)

--     -- Sgᴬ X is a subuniverse of A --------------------------------------
--     lemma SgX_is_Sub {𝔸: algebra σ} (X: set 𝔸): Sub (Sg X):= 
--     assume (f: β) (a: ρ f → 𝔸) (h₀: ∀ i, a i ∈ Sg X), 
--     show 𝔸.snd f a ∈ Sg X, from 
--       assume W (h: Sub W ∧ X ⊆ W), show 𝔸.snd f a ∈ W, from 
--         have h₁: Sg X ⊆ W, from 
--           sInter_mem' W h,
--         have h': ∀ i, a i ∈ W, from assume i, h₁ (h₀ i),
--         (h.left f a h')

--     inductive Y {𝔸: algebra σ} (X: set 𝔸): set 𝔸
--     | var (x : 𝔸) : x ∈ X → Y x
--     | app (f : β) (a : ρ f → 𝔸) : (∀ i, Y (a i)) → Y (𝔸.snd f a)

--     -- Y X is a subuniverse
--     lemma Y_is_Sub {𝔸: algebra σ} (X: set 𝔸): Sub (Y X):= 
--     assume f a (h: ∀ i, Y X (a i)), show Y X (𝔸.snd f a), from 
--     Y.app f a h 

--     -- Y A X is the subuniverse generated by X
--     theorem sg_inductive {𝔸: algebra σ} (X: set 𝔸): Sg X = Y X :=
--       have h₀: X ⊆ Y X, from assume x (h: x ∈ X), 
--         show x  ∈ Y X, from Y.var x h,
--       have h₁: Sub (Y X), from assume f a (h : ∀ x, Y X (a x)), 
--         show Y X (𝔸.snd f a), from Y.app f a h,
--       have inc_l: Sg X ⊆ Y X, from sInter_mem (Y X) h₁ h₀, 
--       have inc_r: Y X ⊆ Sg X, from assume a (h: a ∈ Y X), 
--         show a ∈ Sg X, from
--           have h₂: a ∈ Y X → a ∈ Sg X, from 
--             Y.rec
--             --base: a = x ∈ X
--             ( assume x (hr₁: x ∈ X), 
--               show x ∈ Sg X, from subset_X_of_SgX X hr₁ )
--             --inductive: a = A f b for some b with ∀ i, b i ∈ Sg X
--             ( assume f b (hr₂: ∀ i, b i ∈ Y X) (hr₃: ∀ i, b i ∈ Sg X),
--               show 𝔸.snd f b ∈ Sg X, from SgX_is_Sub X f b hr₃ ),
--           h₂ h,
--       set.subset.antisymm inc_l inc_r

--     definition index_of_sub_above_X {𝔸: algebra σ} 
--     (X: set 𝔸) (C: γ → set 𝔸): γ → Prop:= 
--     λ i, Sub (C i) ∧ X ⊆ (C i) 

--     lemma sInter_mem_of_mem {𝔸: algebra σ} {X: set 𝔸} (x: 𝔸): 
--     x ∈ Sg X ↔ ∀ {R: set 𝔸}, Sub R → X ⊆ R → x ∈ R:= 
--     iff.intro
--       (assume (h: x ∈ Sg X) (R: set 𝔸) (h₁: Sub R) (h₂: X ⊆ R), 
--         show x ∈ R, from h R (and.intro h₁ h₂))
--       (assume (h: ∀ {R: set 𝔸}, Sub R → X ⊆ R → x ∈ R), 
--         show x ∈ Sg X, from h (SgX_is_Sub X) (subset_X_of_SgX X))

--     -- Y is the smallest Sub containing X
--     lemma Y_is_min_Sub {𝔸: algebra σ} (U X: set 𝔸): 
--     Sub U → X ⊆ U → Y X ⊆ U:=
--     assume (h₁: Sub U) (h₂ : X ⊆ U),
--     assume (y: 𝔸)  (p: Y X y), show U y, from 
--       have q: Y X y → Y X y → U y, from 
--         Y.rec

--         --base step: y = x ∈ X
--         ( assume y (h: X y) (h': Y X y), h₂ h )

--         --induction step: y = A f a for some a with ∀ i, a i ∈ Y
--         ( assume f a,
--           assume h₃: ∀ i, Y X (a i), 
--           assume h₄: ∀ i, Y X (a i) → U (a i),
--           assume h₅: Y X (𝔸.snd f a),
--           have h₆: ∀ i, a i ∈ U, from 
--             assume i, h₄ i (h₃ i), show U (𝔸.snd f a), from h₁ f a h₆ ),
--       q p p

--   end subuniverse

-- end ualib

-- -- Miscellaneous Notes

-- -- ⋂₀ is notation for sInter (S : set (set α)) : set α := Inf S,
-- -- and Inf S is defined as follows:
-- --
-- --     Inf := λs, {a | ∀ t ∈ s, a ∈ t },
-- --
-- -- So, if S : set (set α) (i.e., a collection of sets of type α),
-- -- then Inf S is the intersection of the sets in S.

-- namespace ualib
--   section homomorphism

--     parameter {α : Sort u}
--     parameter {β : Sort u}
--     parameter {γ : Type v}
--     parameter {σ : @signature γ}

--     def homomorphic {𝔸 : algebra σ} {𝔹 : algebra σ}
--     (h : 𝔸 → 𝔹) := ∀ f a, h (𝔸.snd f a) = 𝔹.snd f (h ∘ a)

--     -- The following versions merely demostrate 
--     -- syntax variations that are possible in Lean.
--     def homomorphic_terse {𝔸: algebra σ} {𝔹: algebra σ} (h: 𝔸 → 𝔹) := 
--     ∀ f a, h (𝔸.snd f a) = 𝔹.snd f (h ∘ a)

--     def homomorphic_show_types {𝔸: algebra σ} {𝔹: algebra σ} 
--     (h: 𝔸.fst → 𝔹.fst) := 
--     ∀ (f: γ) (a : σ.ρ f → 𝔸.fst), h (𝔸.snd f a) = 𝔹.snd f (h ∘ a)

--   end homomorphism
-- end ualib



