--File: Birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 23 Feb 2020
--UPDATED: 23 Feb 2020
--Notes: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import Preliminaries
--  using (Level; lsuc; _⊔_; _,_; ∣_∣; ⟦_⟧; Pred; _∈_; _∈∈_;im_⊆_; _⊆_)

open import Basic
open import Hom
open import Con
open import Free
open import Subuniverse
--open import Axiom.Extensionality.Propositional

module Birkhoff {i j k : Level} {S : Signature i j}  where

-------------------------------------------------------------------------------
--KERNEL OF A FUNCTION
-----------------------

-- ...as a relation.
ker : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f : A -> B) -> Rel A ℓ₂
ker f x y = f x ≡ f y

-- ...as a binary predicate.
KER : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f : A -> B) -> Pred (A × A) ℓ₂
KER f (x , y) = f x ≡ f y

-------------------------------------------------------------------------------
--EQUALIZERS
-------------

--...of functions
𝑬 :   {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂}
  ->  (f g : A -> B) -> Pred A ℓ₂
𝑬 f g x = f x ≡ g x

--..of homs
--EH :  {ℓ₁ ℓ₂ : Level} {𝑨 : Algebra ℓ₁ S} {𝑩 : Algebra ℓ₂ S}
EqHom :  {𝑨 𝑩 : Algebra k S}
  ->  (f g : Hom {i} {j} {k} 𝑨 𝑩) -> Pred ∣ 𝑨 ∣ k
EqHom f g x = ∣ f ∣ x ≡ ∣ g ∣ x

-- (See also Siva's (infix) def of _~_ in the Hom.agda file.)

EqClosed : ∀{𝓸 : ∣ S ∣}{𝑨 𝑩 : Algebra k S}
  ->        (f g : Hom {i} {j} {k} 𝑨 𝑩)
  ->        (𝒂 : (⟦ S ⟧ 𝓸)  → ∣ 𝑨 ∣)
  ->        (∀ x -> (𝒂 x) ∈ (EqHom {𝑨} {𝑩} f g))
         -----------------------------------------------------
   ->    ∣ f ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂) ≡ ∣ g ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂)
EqClosed {𝓸} {𝑨} {𝑩} f g 𝒂 p =  
  begin
     ∣ f ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂)
  ≡⟨ ⟦ f ⟧ 𝓸 𝒂 ⟩
    ⟦ 𝑩 ⟧ 𝓸 (λ i ->  ∣ f ∣ (𝒂 i))
  ≡⟨ cong (⟦ 𝑩 ⟧ _)
       ((∀-extensionality-ℓ₁-ℓ₂ {j} {k} λ x → p x)) ⟩
    ⟦ 𝑩 ⟧ 𝓸 (λ i -> ∣ g ∣ (𝒂 i))  
  ≡⟨ sym (⟦ g ⟧ 𝓸 𝒂) ⟩
    ∣ g ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂)   
  ∎

-- Obs 2.1. Equalizer of homs is a subuniverse.
-- Equalizer 𝑬(f, g) of f, g : Hom 𝑨 𝑩 is a subuniverse of 𝑨.
EqSub : {𝑨 𝑩 : Algebra k S}
  ->    (f g : Hom{i}{j}{k} 𝑨 𝑩)
       -----------------------------
  ->    Subuniverse
EqSub{𝑨}{𝑩} f g =
  mksub (EqHom{𝑨}{𝑩} f g) λ 𝓸 𝒂 x -> EqClosed{𝓸}{𝑨}{𝑩} f g 𝒂 x

-------------------------------------------------------------------------------
--COMPOSITION OF HOMS
---------------------

-- Obs 2.0. Composing homs gives a hom.
-- See also: Siva's (infix) def of _>>>_ in the Hom.agda file.
HCompClosed : ∀{ℓ₁ ℓ₂ ℓ₃ : Level}
  ->       {𝑨 : Algebra ℓ₁ S}
  ->       {𝑩 : Algebra ℓ₂ S}
  ->       {𝑪 : Algebra ℓ₃ S}
  ->       Hom {i} {j} {k} 𝑨 𝑩  ->  Hom {i} {j} {k} 𝑩 𝑪
         -------------------------
  ->       Hom  {i} {j} {k} 𝑨 𝑪
HCompClosed {𝑨 = (A , 𝐹ᴬ)} {𝑪 = (C , 𝐹ᶜ)}
  (f , h₁) (g , h₂) = g ∘ f , γ
    where
      γ :    (𝓸 : ∣ S ∣) (𝒂 : ⟦ S ⟧ 𝓸 -> A)
          ---------------------------------------
        ->   (g ∘ f) (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᶜ 𝓸 (g ∘ f ∘ 𝒂)
      γ 𝓸 𝒂 rewrite h₁ 𝓸 𝒂 = h₂ 𝓸 (f ∘ 𝒂)

-- Obs 2.2. Homs are determined by their values on a generating set (UAFST Ex. 1.4.6.b)
-- If f, g : Hom(𝑨,𝑩), X ⊆ A generates 𝑨, and f|_X = g|_X, then f = g.
-- PROOF.  Suppose the X ⊆ A generates 𝑨 and f|_X = g|_X. Fix an arbitrary a: A.  We show f a = g a.
--         Since X generates 𝑨, ∃ term t (or arity n = ρt, say) and a tuple x: n -> X of generators
--         such that a = t^𝑨 x. Since f|_X = g|_X, f ∘ x = (f x₀, ..., f xₙ) = (g x₀,...,g xₙ) = g ∘ x,
--         so f a = f(t^𝑨 x) = t^𝑩 (f ∘ x) = t^𝑩 (g ∘ x) = g(t^𝑨 x) = g a.     ☐
HomUnique : {𝑨 𝑩 : Algebra k S}
  ->            (X : Pred ∣ 𝑨 ∣ k)
  ->            (f g : Hom{i}{j}{k} 𝑨 𝑩)
  ->            (∀ x -> x ∈ X -> ∣ f ∣ x ≡ ∣ g ∣ x)
              -----------------------------
  ->            (∀ a -> a ∈ Sg {𝑨 = 𝑨} X -> ∣ f ∣ a ≡ ∣ g ∣ a)
HomUnique {𝑨} {𝑩} X f g fx≡gx a (var x) = (fx≡gx) a x
HomUnique {𝑨} {𝑩} X f g fx≡gx a (app 𝓸 {𝒂} im𝒂⊆SgX) = 
  begin
    ∣ f ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂)
  ≡⟨ ⟦ f ⟧ 𝓸 𝒂 ⟩
    ⟦ 𝑩 ⟧ 𝓸 (∣ f ∣ ∘ 𝒂)
  ≡⟨ cong (⟦ 𝑩 ⟧ _)
     (∀-extensionality-ℓ₁-ℓ₂{j}{k}
       λ i₁ -> HomUnique{𝑨}{𝑩}
               X f g fx≡gx (𝒂 i₁)(im𝒂⊆SgX i₁)
     )
   ⟩
    ⟦ 𝑩 ⟧ 𝓸 (∣ g ∣ ∘ 𝒂)
  ≡⟨ sym (⟦ g ⟧ 𝓸 𝒂) ⟩
    ∣ g ∣ (⟦ 𝑨 ⟧ 𝓸 𝒂)
  ∎

-- Obs 2.3. If A, B are finite and X generates 𝑨, then |Hom(𝑨, 𝑩)| ≤ |B|^|X|.
-- PROOF. By Obs 2, a hom is uniquely determined by its restriction to a generating set.
--   If X generates 𝑨, then since there are exactly |B|^|X| functions from X to B, the result holds. □


------------------------------------------------------
-- Obs 2.4. Factorization of homs.
-- If f ∈ Hom(𝑨, 𝑩), g ∈ Hom(𝑨, 𝑪), g epic, Ker g ⊆ Ker f, then ∃ h ∈ Hom(𝑪, 𝑩), f = h ∘ g.
--
--         𝑨---f---> 𝑩
--          \       7
--           \     /
--          g \   / ∃h
--             v /
--              𝑪
--
-- To do this constructively, we need the following
-- Fact. The inverse of an Epic function is total.

EInv : {𝑨 𝑪 : Algebra k S} 
  ->    (g : Hom{i}{j}{k} 𝑨 𝑪)
  ->    Epic ∣ g ∣
        -----------------------
  ->    ∣ 𝑪 ∣ -> ∣ 𝑨 ∣
EInv{𝑨}{𝑪} g gEpic = (λ c → EpicInv ∣ g ∣ gEpic c)

-- EInv_isInv : {𝑨 𝑪 : Algebra k S} 
--   ->         (g : Hom 𝑨 𝑪)
--   ->         (gEpic : Epic ∣ g ∣)
--   ->          (ginv : Hom 𝑪 𝑨)
--   ->          ginv ≡ EHInv g gEpic
--        -----------------------------------------------------
--   ->   (∣ g ∣ ∘ ∣ ginv ∣ ≡ ∣ id 𝑪 ∣ × ∣ ginv ∣ ∘ ∣ g ∣ ≡ ∣ id 𝑨 ∣)
-- EHInv_isInv = {!!}

homFactor : {𝑨 : Algebra k S}{𝑩 : Algebra k S}{𝑪 : Algebra k S}
  ->        (f : Hom{i}{j}{k} 𝑨 𝑩)
  ->        (g : Hom{i}{j}{k} 𝑨 𝑪)
  ->        KER ∣ g ∣ ⊆ KER ∣ f ∣
  ->        Epic ∣ g ∣
      --------------------------------------------------
  ->   ∃ λ (h : Hom{i}{j}{k} 𝑪 𝑩) -> ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣
homFactor{𝑨}{𝑩}{𝑪}   -- = (A , 𝐹ᴬ)}{𝑩 = (B , 𝐹ᴮ)}{𝑪 = (C , 𝐹ᶜ)}
  f g Kg⊆Kf gEpic = ((λ c → ∣ f ∣ (EpicInv ∣ g ∣ gEpic c)) , {!hIsHomCB!}) , {!!}
  where
    hIsHomCB = λ 𝓸 𝒄 ->
      let gInv = λ c -> (EpicInv ∣ g ∣ gEpic) c in 
        begin
          ∣ f ∣ (gInv (⟦ 𝑪 ⟧ 𝓸 𝒄))
        ≡⟨⟩
          ∣ f ∣ (gInv (⟦ 𝑪 ⟧ 𝓸 (identity {k} ∣ 𝑪 ∣ ∘ 𝒄)))
        ≡⟨ cong ∣ f ∣ ((cong gInv) (cong (⟦ 𝑪 ⟧ 𝓸)
           (∀-extensionality-ℓ₁-ℓ₂ {j}{k} λ x →
             begin
               (𝒄 x)
             ≡⟨ refl ⟩
               identity ∣ 𝑪 ∣ (𝒄 x)
             ≡⟨ {!!} ⟩
               (∣ g ∣ ∘ (EpicInv ∣ g ∣ gEpic)) (𝒄 x)
             ∎
           )))
         ⟩
          ∣ f ∣ (gInv (⟦ 𝑪 ⟧ 𝓸 (∣ g ∣ ∘ (gInv ∘ 𝒄))))
        ≡⟨ cong ∣ f ∣  {!!} ⟩
          ∣ f ∣ (gInv (∣ g ∣ (⟦ 𝑨 ⟧ 𝓸 (gInv ∘ 𝒄))))
        ≡⟨ cong ∣ f ∣ {!!} ⟩
          ∣ f ∣ ( ⟦ 𝑨 ⟧ 𝓸 (gInv ∘ 𝒄))
        ≡⟨ ⟦ f ⟧ 𝓸 (gInv ∘ 𝒄) ⟩
          ⟦ 𝑩 ⟧ 𝓸 (λ i₁ → ∣ f ∣ (gInv (𝒄 i₁)))
        ∎


-- PROOF. We define h ∈ Hom 𝑪 𝑩 as follows: Fix c ∈ C. Since g is surjective, g^{-1}{c} ⊆ A ≠ ∅,
--   and ker g ⊆ ker f implies every a ∈ g^{-1}{b} is mapped by f to a single b ∈ B.
--   Label this unique element bc. That is, f(a) = bc, for all a ∈ g^{-1}{c}. For each such c,
--   and its associated bc, define h(c) = bc.

--   Consider the foregoing "construction" of the function h.
--   While it's true that for each b ∈ B there exists a cb such that h(a) = cb for all a ∈ g^{-1}{b},
--   it's also true that we have no means of producing such cb constructively. One could argue that
--   each cb is easily computed as cb = h(a) for some (every) a ∈ g^{-1}{b}. But this requires
--   producing a particular a ∈ g^{-1}{b} to use as "input" to the function h. How do we select such
--   an element from the (nonempty) set g^{-1}{b}?
--      
--   Unfortunately, it seems we must appeal to the Axiom of Choice here, and concede that the
--   function k cannot be constructively defined. Nonetheless, we forge ahead (nonconstructively) and
--   define k as described above, using the Axiom of Choice to compute a cb for each b ∈ B.
--
--   It is then easy to see that k ∘ g = h.  Indeed, for each a ∈ A, we have a ∈ g^{-1}{g(a)}, so
--   k(g(a)) = h(a) by definition.
--
--   Finally, to prove that k is a hom, fix an operation symbol f ∈ 𝓕 and a tuple b: Fin(ρ f) -> B; we
--   must show f^𝑪 (k ∘ b) = k (f^𝑩(b)).
--
--   Let a : Fin(ρ f) -> A be such that g ∘ a = b.  Then the left hand side is
--   f^𝑪 (k ∘ g ∘ a) = f^𝑪 (h ∘ a), which is equal to h (f^𝑨 (a)) since h is a hom. Therefore,
--
--   f^𝑪(k ∘ b) = f^𝑪(k ∘ g ∘ a) = f^𝑪(h ∘ a) = h(f^𝑨(a)) = (k ∘ g)(f^𝑨(a)) = k(f^𝑩(g ∘ a)) = k(f^𝑩(b)),
--
--   as desired, where the penultimate equality holds by virtue of the fact that g is a hom. ☐


-- Obs 2.5. Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.

-- Obs 2.6. Inductive version of Sg^𝑨.                                                        
-- Let 𝑨 be an algebra in the signature S and A₀ a subset of A. Define, by recursion on n,
-- the sets Aₙ as follows: If A₀ = ∅, then Aₙ = ∅ for all n<ω. If A₀ ≠ ∅, then A_{n+1} =
-- Aₙ ∪ { f a ∣ f ∈ F, a ∈ Fin(ρ f) -> Aₙ}. Then the subuniverse of 𝑨 generated by A₀ is
-- Sg^𝑨(A₀) = ⋃ₙ Aₙ.
-- PROOF.
--   Let Y := ⋃ₙ Aₙ. Clearly Aₙ ⊆ Y ⊆ A, for every n < ω. In particular A = A₀ ⊆ Y. We first show that
--   Y is a subuniverse of 𝑨. Let f be a basic k-ary operation and let a: Fin(k) -> Y be a k-tuple of
--   elements of Y. From the construction of Y, ∃ n < ω, ∀ i, (a i) ∈ Aₙ. From its definition,
--   f a ∈ A_{n+1} ⊆ Y. Since f was arbitrary, Y is a subuniverse of 𝑨 containing A₀. Thus, Sg^𝑨(A₀) ⊆ Y.
--   For the opposite inclusion, we check that Aₙ ⊆ Sg^𝑨(A₀), for each n. Clearly, A₀ ⊆ Sg^𝑨(A₀).
--   Assume Aₙ ⊆ Sg^𝑨(A₀). We must show A_{n+1} ⊆ Sg^𝑨(A₀). If b ∈ A_{n+1} - Aₙ, then b = f a for a basic
--   k-ary operation f and some a: Fin(k) -> Aₙ.  But ∀ i, a i ∈ Sg^𝑨(A₀), and this latter object is a
--   subuniverse, so b ∈ Sg^𝑨(X) as well. Therefore, A_{n+1} ⊆ Sg^𝑨(A₀), as desired.    ☐ 

-- Obs 2.7. Inductive version of Clo(F).  (UAFST Thm 4.3)
-- Let A be a set and let F ⊆ Op(A):= ⋃ₙ A^Aⁿ be a collection of operations on A.
-- Define F_0 := Proj(A) (the set of projection operations on A) and for all 0 ≤ n < ω,
-- let F_{n+1} := Fₙ ∪ { f g | f ∈ F, g : Fin(ρ f) -> Fₙ ∩ (Fin(ρg) -> A) }.
-- Then Clo(F) = ⋃ₙ Fₙ.
-- PROOF.
--   Let F̄ = ⋃ₙ Fₙ. By induction, every Fₙ is a subset of Clo(F). Thus, F ⊆ Clo(F).
--   For the converse inclusion, we must show F` is a clone that contains F. Obviously F contains the
--   projection operations, F₀ ⊆ F̄. For every f ∈ F, we have f πᵏ ∈ F₁ ⊆ F̄, where k := ρ f.
--   We must show that F̄ is closed under generalized composition. This follows from the following subclaim.
--   SUBCLAIM. If f ∈ Fₙ and all entries of g := (g₀, ..., g_{ρf - 1} ∈ Fₘ are k-ary, then f g ∈ F_{n+m},
--             where we have defined g: Fin(ρ f) -> (k -> A) -> A to be the tuple given by g i = gᵢ for
--             each 0 ≤ i < ρ f.
--
--   By induction on n: If n = 0 then f is a projection, so f g = gᵢ ∈ Fₘ for some 0 ≤ i < ρ f.
--   Assume (IH) claim holds for n and f ∈ F_{n+1} - Fₙ.
--   By def, ∃ t-ary op fᵢ ∈ F, ∃ t-tuple, h = (h₀, ..., h_{t-1}) ∈ t -> Fₙ, such that f = fᵢ h.
--   (N.B. h: Fin(t) -> (Fin(ρ f) -> A) -> A is given by h(j) = hⱼ, and the arity of each hᵢ must
--   be equal to that of f, namely ρ f.) By (IH) for each i ≤ k, hᵢ = hᵢ g ∈ F_{n+m}, where as
--   above g = (g₀,...,g_{k-1}). By def, f₁ h' ∈ F_{n+m+1} = F_{(n+1)+m}.
--   Since f₁ h' = f₁ ∘ (h₁ g, ..., hₜ g) = f g, the claim is proved. □

-- Obs 2.8. Lift of a map h : X -> A extends uniquly to a hom 𝑻(X) -> 𝑨.  (UAFST Thm 4.21)
-- 1. 𝑻 := 𝑻_σ(X) is generated by X.
-- 2. ∀ 𝑨 = ⟨A, F^𝑨⟩, ∀ g: X → A, ∃! hom h: 𝑻 → 𝑨,  h|_X = g.
-- PROOF.
--   The def of 𝑻 exactly parallels the construction in Obs 6 above. That accounts for the
--   1st assertion. For the 2nd assertion, define h t by induction on the height, |t|, of t.
--   Suppose |t| = 0.  Then t ∈ X ∪ F₀. If t ∈ X, then define h t = g t. If t ∈ F₀, then
--   let h t = t^𝑨. For the inductive step, assume |t| = n+1. Then t = f s for some f ∈ F
--   and s: Fin(ρ f) -> Tₙ, where for each 0 ≤ i< ρ f the term s i has height at most n.
--   Define h t = f^𝑨(h ∘ s) = f^𝑨(h s₁, ..., h sₖ). Then h is a hom that agrees with g on X.
--   The uniqueness of h follows from Obs 2. ☐

-- Obs 2.9. Homs commute with terms. (UAFST Thm 4.32)
-- Let t ∈ T_σ (X) be an n-ary term and let t^𝑨 be its interpretation in 𝑨, so
-- t^𝑨 a = t^𝑨 (a 0, a 1, ..., a (n-1)), for each a : Fin(n) -> A. Similarly,
-- t^𝑩: (Fin(n) -> B) -> B is the interpretation of t in 𝑩. If g: 𝑨 → 𝑩 is a hom,
-- then g ∘ a: Fin(n) → B is the n-tuple whose i-th component is (g ∘ a) i = g(a i),
-- and g(t^𝑨 a) = t^𝑩(g ∘ a) holds.
-- PROOF. Easy induction on term height |t|. ☐

-- Obs 2.10. Terms respect congruences.
-- If θ is a congruence of 𝑨 and a, a': Fin(n) -> A are n-tuples over A, then
--     (a, a') ∈ θ  ⟹  (t^𝑨 a, t^𝑨 a') ∈ θ.
-- PROOF. Apply Obs 8 with ⟨B, F^𝑩⟩ = ⟨A, F^𝑨⟩/θ = ⟨A/θ, F^{𝑨/θ}⟩ and g = the canonical hom. ☐

-- Obs 2.11 (on subuniverse generation as image of terms).
-- If Y is a subset of A, then
--   Sg^{𝑨}(Y) = { t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: Fin(ρ t) -> Y }.
-- PROOF.
--   Induction on the height of t shows that every subuniverse is closed under the action
--   of t^𝑨. Thus the right-hand side is contained in the left. On the other hand, the
--   right-hand side is a subuniverse that contains the elements of Y (take t = x₁), so it
--   contains Sg^{𝑨}(Y), as the latter is the smallest subuniverse containing Y. ☐

-- Obs 2.12. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦)
-- satisfies exaxtly the same set of identities as does 𝒦.
-- PROOF. We prove the result for 𝖧(𝒦).
--        𝒦 ⊆ 𝖧(𝒦), so Th 𝖧 (𝒦) ⊆  Th 𝒦.... 

-- Obs 2.13. 𝒦 ⊧ p ≈ q iff ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨`. (UAFST Lem 4.37)
-- PROOF.
-- ⇒ Assume 𝒦 ⊧ p ≈ q. Fix 𝑨 ∈ 𝒦 and h ∈ Hom(𝑻(X_ω), 𝑨). We must show ∀ a: Fin(ρ p) -> A that
--    h(p^𝑨 a) = h(q^𝑨 a). Fix a: Fin(ρ p) -> A`. By 𝑨 ⊧ p ≈ q we have p^𝑨 = q^𝑨 which implies
--    p^𝑨(h ∘ a) = q^𝑨(h ∘ a). Since h is a hom, we obtain h(p^𝑨 a) = h(q^𝑨 a), as desired.
-- ⇐ Assume ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨. We must show 𝒦 ⊧ p ≈ q.
--    Fix 𝑨 ∈ 𝒦 and a: Fin(ρ p) -> A. We must prove p^𝑨 a = q^𝑨 a`. Let h₀ : X_ω -> A be a function
--    with h₀ x i = a i for all 0≤ i < ρ p, for some x: Fin(ρ p) -> X_ω. By Obs 6, h₀ extends to a
--    homomorphism h from 𝑻(X_ω) to 𝑨. By assumption h p^𝑨 = h q^𝑨, and since h is a homomorphism,
--    p^𝑨 a =  p^𝑨(h ∘ x) = h(p^𝑨 x) = h(q^𝑨 x) = q^𝑨 (h ∘ x) = q^𝑨 a, so p^𝑨 a = q^𝑨 a. ☐

-- Obs 2.14. Let 𝒦 be a class of algebras and p ≈ q an equation. The following are equivalent.
-- 1. 𝒦 ⊧ p ≈ q.
-- 2. (p, q) belongs to the congruence λ_𝒦 on 𝑻(X_ω).
-- 3. 𝑭_𝒦(X_ω) ⊧ p ≈ q.
-- PROOF.
--   We shall show (1) ⟹ (3) ⟹ (2) ⟹ (1).  Recall that 𝑭_𝒦(X_ω) = 𝑻/λ ∈ 𝖲 𝖯 (𝒦).
--   From (1) and Lemma 4.36 of :term:`UAFST` we have 𝖲 𝖯 (𝒦) ⊧ p ≈ q. Thus (3) holds.
--   From (3), p^𝑭 [x] = q^𝑭 [x], where [x]: Fin(ρ p) → 𝑭_𝒦 (X_ω) is defined by [x] i = xᵢ/λ.
--   From the def of 𝑭, p^𝑻 x ≡λ q^𝑻 x, from which (2) follows since p = p^𝑻 x and q = q^𝑻 x.
--   Finally assume (2). We wish to apply Lemma 4.37 of UAFST. Let 𝑨 ∈ 𝒦 and h ∈ Hom(𝑻, 𝑨).
--   Then 𝑻/ker h ∈ 𝖲 (𝑨) ⊆ 𝖲(𝒦) so ker h ⊇ λ.  Thus, (2) implies h p = h q hence (1) holds. ☐

-- The last result tells us that we can determine whether an identity is true in a variety by
-- consulting a particular algebra, namely 𝑭(X_ω). Sometimes it is convenient to work with algebras
-- free on other generating sets besides X_ω. The following corollary takes care of that for us.

-- Obs 2.15. Let 𝒦 be a class of algebras, p, q terms (say, n-ary), Y a set, and y₁,..., yₙ
-- distinct elements of Y. Then 𝒦 ⊧ p ≈ q iff p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦}(Y)(y₁, ..., yₙ).
-- In particular, 𝒦 ⊧ p ≈ q iff 𝑭_𝒦(Xₙ) ⊧ p ≈ q.
-- PROOF. Since 𝑭_𝒦(Y) ∈ 𝖲 𝖯 (𝒦), the left-to-right direction uses the same argument as in
--   Thm 4.38 of UAFST. (See Obs 14 above.) So assume that p^{𝑭_𝒦(Y)}(y₁,..., yₙ) =
--   q^{𝑭_𝒦(Y)}(y₁,..., yₙ). To show that 𝒦 ⊧ p ≈ q, let 𝑨= ⟨ A, f^𝑨 ⟩ ∈ 𝒦 and a₁, ..., aₙ ∈ A.
--   We must show p^𝑨(a₁,..., aₙ) = q^𝑨(a₁,...,aₙ)`. There is a hom h: 𝔽_𝒦(Y) -> (A, f^𝑨) such
--   that h(yᵢ) = aᵢ for i ≤ n. Then p^𝑨(a₁, ..., aₙ) = p^𝑨(h(y₁), ..., h(yₙ)) = h(p^{𝑭_𝒦(Y)}(y₁, ...,yₙ))
--   = h(q^{𝑭_𝒦(Y)}(y₁, ...,yₙ)) = q^𝑨(h(y₁), ..., h(yₙ)) = q^𝑨(a₁, ..., aₙ).
--   It now follows from Obs 12 that every equational class is a variety.  ☐
--
--        (The converse of Obs 2.15 is **Birkhoff's HSP Theorem**.)
--
-- Obs 2.16. Every  finitely  generated  variety  is  locally finite. (UAFST Thm 3.49)
-- (This is not needed for the HSP theorem, but we might want to prove it next.)
--
-- The converse of the last theorem is false.  That is, ∃ loc fin varieties that are not finitely generated
-- (e.g., the variety of p-algebras; see UAFSt Cor. 4.55).


--------------
-- VARIETIES
--------------

--cf Def 1.10 of Bergman
--Let 𝓚 be a class of similar algebras. We write
--  H(𝓚) for the class of all homomorphic images of members of 𝓚;
--  S(𝓚) for the class of all algebras isomorphic to a subalgebra of a member of 𝓚;
--  P(𝓚) for the class of all algebras isomorphic to a direct product of members of 𝓚;
--We say that 𝓚 is closed under the formation of homomorphic images if H(𝓚) ⊆ 𝓚,
--and similarly for subalgebras and products.
--Notice that all three of these "class operators" are designed so that for any
--class 𝓚, H(𝓚), S(𝓚), P(𝓚) are closed under isomorphic images.
--On those rare occasions that we need it, we can write I(𝓚) for the class of algebras
--isomorphic to a member of 𝓚.
--Finally, we call 𝓚 a VARIETY if it is closed under each of H, S and P.

-- contains : {A : Set} -> (L : List A) -> A -> Prp
-- contains [] a = ⊥
-- contains (h :: tail) a = (h ≡ a) ⋁ (contains tail a)

--data class-of-algebras : Set where

-- --Hom-closed
-- H-closed : (𝓚 : Pred (algebra S)) -> Prp
-- H-closed 𝓚 = ∀ (A : algebra S)  ->  (𝓚 A)
--   ->     (∃ θ : Con A)   ->   (∃ C : algebra S)
--   ->     (𝓚 C) ∧ (A / θ ≅ C)

-- --Sub-closed
-- -- SC : (𝓚 : List (algebra S)) -> Prp
-- -- SC 𝓚 = ∀(A : algebra S) -> (contains 𝓚 A)
-- --   -> (B : subalgebra A) -> (∃ C : algebra S)
-- --   -> (contains 𝓚 C) ∧ B ≃ C
















--====================================================
------------------------------------------------------
-- OLD STUFF
--
-- open import Level
-- open import basic
-- open import subuniverse
-- open algebra
-- open signature
-- open import preliminaries
-- open import Relation.Unary
-- open import Relation.Binary.Core
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; cong; trans; sym)
-- open Eq.≡-Reasoning
-- open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
