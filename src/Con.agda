--File: Congruence.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 22 Feb 2020
--Updated: 23 Feb 2020
--Notes: Based on the parts of the file `basic.agda` (24 Dec 2019).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
open import Basic 

module Con where

-------------------------------------------------------------------
--Equivalence relations and blocks

--a single θ-class of A
[_]_ : {k : Level}{A : Set k} -> (a : A) -> Rel A k -> Pred A _
[ a ] θ = λ x → θ a x

--the collection of θ-classes of A
_//_ : {k : Level} -> (A : Set k) -> Rel A k -> Set _
A // θ = ∃ λ (C : Pred A _) -> (∃ λ a -> C ≡ [ a ] θ)

--The "trivial" or "diagonal" or "identity" relation.
𝟎 : {ℓ : Level} (A : Set ℓ) -> Rel A ℓ
𝟎 A a₁ a₂ = a₁ ≡ a₂

𝟎-isEquiv : {ℓ : Level} {A : Set ℓ} -> IsEquivalence{ℓ}{ℓ}{A} (𝟎 A)
𝟎-isEquiv =
  record
  { refl = λ {x} → refl
  ; sym = sym
  ; trans = λ {i} {j} {k} z z₁ → begin i ≡⟨ z ⟩ j ≡⟨ z₁ ⟩ k ∎
  }
  -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

-- lift a binary relation from pairs to pairs of tuples.
lift-rel : ∀{ℓ₁ : Level} {Idx : Set ℓ₁} {ℓ₂ : Level} {Z : Set ℓ₂}
  ->       Rel Z ℓ₂
          -----------------
  ->       Rel (Idx -> Z) (ℓ₁ ⊔ ℓ₂)
lift-rel R 𝒂₁ 𝒂₂ = ∀ i -> R (𝒂₁ i) (𝒂₂ i)

-- compatibility of a give function-relation pair
compatible-fun : ∀ {ℓ₁ ℓ₂ : Level} {γ : Set ℓ₁} {Z : Set ℓ₂}
  ->             ((γ -> Z) -> Z)
  ->             (Rel Z ℓ₂)
                -----------------------------------------
  ->             Set (ℓ₁ ⊔ ℓ₂)
compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

module _ {i j : Level} {S : Signature i j}  where

  -- relation compatible with an operation
  compatible-op : {k : Level}{𝑨 : Algebra k S} -> ∣ S ∣ -> Rel ∣ 𝑨 ∣ k -> Set (j ⊔ k)
  compatible-op{k}{𝑨} 𝓸 𝓻 = (lift-rel 𝓻) =[ (⟦ 𝑨 ⟧ 𝓸) ]⇒ 𝓻

  --The given relation is compatible with all ops of an algebra.
  compatible : {k : Level}(𝑨 : Algebra k S) -> Rel ∣ 𝑨 ∣ k -> Set (i ⊔ j ⊔ k)
  compatible{k} 𝑨 𝓻 = ∀ 𝓸 -> compatible-op{k}{𝑨} 𝓸 𝓻

  𝟎-compatible-op : {k : Level}{𝑨 : Algebra k S} -> (𝓸 : ∣ S ∣) -> compatible-op{k}{𝑨} 𝓸 (𝟎 ∣ 𝑨 ∣)
  𝟎-compatible-op{k}{𝑨} = λ 𝓸 x -> cong (⟦ 𝑨 ⟧ 𝓸) (extensionality x)

  𝟎-compatible : {k : Level}{𝑨 : Algebra k S} -> compatible 𝑨 (𝟎 ∣ 𝑨 ∣)
  𝟎-compatible{k}{𝑨} = λ 𝓸 args -> 𝟎-compatible-op{k}{𝑨} 𝓸 args

  -- Congruence relations
  Con : {k : Level}(𝑨 : Algebra k S)
         -----------------------
    ->    Set (i ⊔ j ⊔ lsuc k)
  --  ->    Set (lsuc i ⊔ lsuc j ⊔ lsuc k)
  Con{k} 𝑨 = ∃ λ (θ : Rel ∣ 𝑨 ∣ k)
            -> IsEquivalence θ × compatible 𝑨 θ

  con : {k : Level} (𝑨 : Algebra k S)
         -----------------------
    ->   Pred (Rel ∣ 𝑨 ∣ k) _
  con 𝑨 = λ θ → IsEquivalence θ × compatible 𝑨 θ
          --  -> 
  record Congruence{k : Level} (𝑨 : Algebra k S) : Set (i ⊔ j ⊔ lsuc k) where
    constructor mkcon
    field
      ∥_∥ : Rel ∣ 𝑨 ∣ k
      Compatible : compatible 𝑨 ∥_∥
      IsEquiv : IsEquivalence ∥_∥
  open Congruence 

  --The "trivial" or "diagonal" or "identity" relation.
  ⟦𝟎⟧ : {k : Level}(𝑨 : Algebra k S) -> Congruence 𝑨
  ⟦𝟎⟧{k} 𝑨 = mkcon (𝟎 ∣ 𝑨 ∣)
                (𝟎-compatible{k}{𝑨})
                (𝟎-isEquiv )

  _/_ : {k : Level}(𝑨 : Algebra k S)
    ->  Congruence 𝑨
       -----------------------
    ->  Algebra (lsuc k) S
  𝑨 / θ = ( ( ∣ 𝑨 ∣ // ∥ θ ∥ ) , -- carrier
             ( λ 𝓸 args        -- operations
                 -> ( [ ⟦ 𝑨 ⟧ 𝓸 (λ i₁ -> ∣ ⟦ args i₁ ⟧ ∣) ] ∥ θ ∥ ) ,
                    ( ⟦ 𝑨 ⟧ 𝓸 (λ i₁ -> ∣ ⟦ args i₁ ⟧ ∣) , refl )
             )
           )

