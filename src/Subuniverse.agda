--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 26 Feb 2020
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import Preliminaries
open import Basic
open import Free
open import Hom

module Subuniverse where

private
  variable
    i j k l : Level
    S : Signature i j
    𝑨 : Algebra k S
    𝑩 : Algebra l S

Subuniverses : {S : Signature i j} → (𝑨 : Algebra k S) →
              ---------------------------------------
               Pred (Pred ∣ 𝑨 ∣ l) (i ⊔ j ⊔ k ⊔ l)
Subuniverses {S = S} 𝑨 B =
  (𝓸 : ∣ S ∣ ) -> (𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ ) ->  Im 𝒂 ⊆ B → ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ B

module _ {i j k : Level} {S : Signature i j} where
  -- To keep A at same universe level as ∃ P , B, force P to live in the same universe
  -- We need to do this so that both A and ∃ P , B can be classified by the same predicate SClo
  data _is-supalgebra-of_ (𝑨 : Algebra k S) : Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k)) where
    mem : {P : Pred ∣ 𝑨 ∣ k} {B : (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) (∃ P)} →
            ((𝓸 : ∣ S ∣) → (x : ⟦ S ⟧ 𝓸 → ∃ P) → ∣ B 𝓸 x ∣ ≡ ⟦ 𝑨 ⟧ 𝓸 (λ i → ∣ x i ∣)) →
          𝑨 is-supalgebra-of (∃ P , B)

  _is-subalgebra-of_ : Algebra _ S → Algebra _ S → Set _
  𝑩 is-subalgebra-of 𝑨 = 𝑨 is-supalgebra-of 𝑩

module _ {i j k : Level} {S : Signature i j}   where
  record Subuniverse  {𝑨 : Algebra k S} : Set (i ⊔ j ⊔ lsuc k) where
    constructor mksub
    field
      sset  : Pred ∣ 𝑨 ∣ k
      isSub : sset ∈ Subuniverses 𝑨

module _ {i j k} {S : Signature i j} {𝑨 : Algebra k S} {X : Set k} where
  SubunivAlg : {B : Pred ∣ 𝑨 ∣ k} -> B ∈ Subuniverses 𝑨 -> Algebra k S
  SubunivAlg{B} P = ∃ B , λ 𝓸 x → ⟦ 𝑨 ⟧ 𝓸 (∣_∣ ∘ x) , P 𝓸 (∣_∣ ∘ x) (⟦_⟧ ∘ x)
  --  SubunivAlg = ∃ B , λ 𝓸 x → ⟦ 𝑨 ⟧ 𝓸 (proj₁ ∘ x) , P 𝓸 (proj₁ ∘ x) (proj₂ ∘ x)

  subuniv-to-subalg : {B : Pred ∣ 𝑨 ∣ k} -> (P : B ∈ Subuniverses 𝑨) -> (SubunivAlg{B} P) is-subalgebra-of 𝑨
  subuniv-to-subalg P = mem λ _ _ → refl

  subalg-to-subuniv :  {P : Pred ∣ 𝑨 ∣ k} {B : (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) (∃ P)}
    ->                 (∃ P , B) is-subalgebra-of 𝑨 -> P ∈ Subuniverses 𝑨
  subalg-to-subuniv{P}{B} sub = λ 𝓸 𝒂 x → {!!}


module _ {i j k l : Level} {S : Signature i j} {𝑨 : Algebra k S} where
  data Sg (X : Pred ∣ 𝑨 ∣ l) : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k ⊔ l) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app :  (𝓸 : ∣ S ∣) {𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ }
      →   Im 𝒂 ⊆ Sg X
      ------------------
      → ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Sg X

sgIsSub : ∀ {i j k l} {S : Signature i j} {𝑨 : Algebra k S}
          (X : Pred ∣ 𝑨 ∣ l) → Sg X ∈ Subuniverses 𝑨
sgIsSub _ 𝓸 𝒂 α = app 𝓸 α

-- Even though sgIsSub {i} {j} {k} {k} {S} {𝑨} X has type Sg X ∈ Subuniverses 𝑨
-- SubunivAlg refuses to take it as an argument!!! What's going on???
--postulate hom-sg-to-fun : ∀ {i j k l} {S : Signature i j} {𝑨 : Algebra k S} {𝑩 : Algebra l S} {X : Pred ∣ 𝑨 ∣ k} → Hom (SubunivAlg {i} {j} {k} {S} {𝑨} {B = Sg X} (sgIsSub ?)) 𝑩 → (∃ X → ∣ 𝑩 ∣)
--hom-sg-to-fun = {!!}

-- WARNING: if you move X into the scope of sgIsSmallest, you get the following error:
-- "An internal error has occurred. Please report this as a bug.
--  Location of the error: src/full/Agda/TypeChecking/Monad/Context.hs:119"
-- I think it has to do with variable generalization
module _ {X : Pred ∣ 𝑨 ∣ l} where
  sgIsSmallest : {m : Level} {Y : Pred ∣ 𝑨 ∣ m}
    → Y ∈ Subuniverses 𝑨
    → X ⊆ Y
    -----------------
    → Sg X ⊆ Y
  -- By induction on x ∈ Sg X, show x ∈ Y
  sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X
  sgIsSmallest {Y = Y} YIsSub X⊆Y (app 𝓸 {𝒂} im𝒂⊆SgX) = app∈Y where
    -- First, show the args are in Y
    im𝒂⊆Y : Im 𝒂 ⊆ Y
    im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

    -- Since Y is a subuniverse of 𝑨, it contains the application of 𝓸 to said args
    app∈Y : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Y
    app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y

-- Same issue here as above
-- Obs 2.5. Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.
module _ {m : Level} {I : Set l} {A : I → Pred ∣ 𝑨 ∣ m} where
  sub-inter-is-sub : ((i : I) → A i ∈ Subuniverses 𝑨) → ⋂ I A ∈ Subuniverses 𝑨
  sub-inter-is-sub Ai-is-Sub 𝓸 𝒂 im𝒂⊆⋂A = α where
    α : ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ ⋂ I A
    -- Suffices to show (i : I) → ⟦ A ⟧ 𝓸 𝒂 ∈ A i
    -- Immediate from A i being a subuniverse
    α i = Ai-is-Sub i 𝓸 𝒂 λ j → im𝒂⊆⋂A j i

-- Hom is subuniverse

module _ {S : Signature i j} {𝑨 𝑩 : Algebra k S} (f : Hom 𝑨 𝑩) where
  HomImage : ∣ 𝑩 ∣ -> Set k
  HomImage = λ b -> Image ∣ f ∣ ∋ b

  hom-image-is-sub : HomImage ∈ Subuniverses 𝑩
  hom-image-is-sub 𝓸 𝒃 𝒃∈Imf =
    let 𝒂 = λ x -> Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) in
    let 𝒃≡𝒄 = ∀-extensionality-ℓ₁-ℓ₂
              (λ x -> InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)) in 
    let fin = trans (⟦ f ⟧ 𝓸 𝒂) (cong ( ⟦ 𝑩 ⟧ 𝓸 ) 𝒃≡𝒄) in
      eq (⟦ 𝑩 ⟧ 𝓸 (λ x → 𝒃 x)) ( ⟦ 𝑨 ⟧ 𝓸 𝒂) (sym fin)

-- Paper-pencil-proof.
-- Let 𝓸 be an op symbol.  Let args : ⟦ S ⟧ 𝓸 -> ∣ 𝑩 ∣ be a (⟦ S ⟧ 𝓸)-tuple of elements ∣ 𝑩 ∣.
-- Assume ∀ i₁ -> args i₁ ∈ Image ∣ f ∣.
-- We must show (⟦ 𝑩 ⟧ 𝓸) args ∈ Image ∣ f ∣.
-- ∀ i₁ -> args i₁ ∈ Image ∣ f ∣ implies
-- ∃ 𝒂 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣ such that ∣ f ∣ ∘ 𝒂 = args.
-- i.e., ∀ i₁ ->  ∣ f ∣ 𝒂 i₁ = args i₁.
-- Sine f : Hom 𝑨 𝑩, we have
-- (⟦ 𝑩 ⟧ 𝓸) args = (⟦ 𝑩 ⟧ 𝓸) (∣ f ∣ ∘ 𝒂) = ∣ f ∣ ⟦ 𝑨 ⟧ 𝓸 𝒂 ∈ Image ∣ f ∣ 

module _  {S : Signature i j} {𝑨 𝑩 : Algebra k S} {B : Pred ∣ 𝑨 ∣ l} {P : Pred ∣ 𝑨 ∣ k} {B : (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) (∃ P)} {X : Set k} where

  -- Subuniverses are closed under the action of term operations.
  sub-term-closed : P ∈ Subuniverses 𝑨
    ->              (𝒕 : Term)
    ->              (𝒙 : X -> ∣ 𝑨 ∣)
    ->              (∀ i -> 𝒙 i ∈ P)
                 -------------------------
    ->              ((𝒕 ̇ 𝑨) 𝒙) ∈ P
  sub-term-closed P≤𝑨 (generator x) 𝒙 𝒙∈P = 𝒙∈P x
  sub-term-closed P≤𝑨 (node 𝓸 𝒕) 𝒙 𝒙∈P =
    P≤𝑨 𝓸 (λ z → (𝒕 z ̇ 𝑨) 𝒙) (λ x → sub-term-closed P≤𝑨 (𝒕 x) 𝒙 𝒙∈P)
    -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

  subalg2subuniv = subalg-to-subuniv{i}{j}{k}{S}{𝑨}{X}{P}{B}
  
  interp-sub : (sub : (∃ P , B) is-subalgebra-of 𝑨)
    ->         (p : Term)
    ->         (x  : X -> ∣ 𝑨 ∣ )
    ->         (Imx⊆P : Im x ⊆ P)
    ->         (p ̇ (∃ P , B)) (img x P Imx⊆P) ≡
               ((p ̇ 𝑨) x , sub-term-closed (subalg2subuniv sub) p x Imx⊆P )
  interp-sub sub p x Imx⊆P = {!!}

-- subalg-to-subuniv :  {P : Pred ∣ 𝑨 ∣ k} {B : (𝓸 : ∣ S ∣) -> Op (⟦ S ⟧ 𝓸) (∃ P)}
--     ->                 (∃ P , B) is-subalgebra-of 𝑨 -> P ∈ Subuniverses 𝑨

-- interp-sub : (𝑩 : Algebra k S)
  --   ->         (sub : 𝑩 is-subalgebra-of 𝑨)
  --   ->         (p : Term)
  --   ->         (x  : X -> ∣ 𝑨 ∣ )
  --   ->         (p ̇ 𝑩) (λ x -> P x ) ≡  (p ̇ 𝑨) x
  -- interp-sub (generator x₁) x = {!!}
  -- interp-sub (node 𝓸 𝒕) x = {!!}


  -- interp-sub : {ℓ : Level}{I : Set ℓ}
  --   ->         (p : Term) -> (𝑩 : Algebra k S)
  --   ->         (sub : 𝑩 is-subalgebra-of 𝑨)
  --   ->         (x  : X -> ∣ 𝑨 ∣ )
  --   ->         Im x ⊆ ∣ 𝑩 ∣
  --   ->         (p ̇ 𝑩) x ≡  (p ̇ 𝑨) x
  -- interp-sub (generator x₁) x = {!!}
  -- interp-sub (node 𝓸 𝒕) x = {!!}





  -- Obs 2.11 (on subuniverse generation as image of terms) (cf. UAFST Thm 4.32(3))
  -- If Y is a subset of A, then
  --    Sg(Y) = {t(a₁,...,aₙ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.
  -- Or, in our notation, 
  --   Sg^{𝑨}(Y) = { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y }.
  -- Paper-pencil-proof.
  --   Induction on the height of t shows that every subuniverse is closed
  --   under the action of t^𝑨. Thus the right-hand side (RHS) is contained
  --   in the left. The formalization is given by `sub-term-closed`; it proves
  --      Sg^{𝑨}(Y) ⊇ { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y }.
  --   On the other hand, the RHS is a subuniverse that contains Y (take t = x₁), so
  --   contains Sg^{𝑨}(Y), as the latter is the smallest subuniverse containing Y.
  --   So, we prove Sg^{𝑨}(Y) ⊆ { 𝒕^𝑨 𝒂 : 𝒕 ∈ Term{X}, 𝒂 : X -> Y } following these steps:
  -- 1. The image of Y under all terms, `TermImage Y`, is a subuniverse of 𝑨.
  --    That is, TermImageY = ⋃{𝒕:Term} Image (𝒕 ̇ 𝑨) Y ≤ 𝑨.
  -- 2. Y ⊆ TermImageY (obvious)
  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y (see `sgIsSmallest`)
  --    so Sg^𝑨(Y) ⊆ TermImageY ∎

  data TermImage (Y : Pred ∣ 𝑨 ∣ k) : Pred ∣ 𝑨 ∣ (i ⊔ j ⊔ k) where
    var : ∀ {y : ∣ 𝑨 ∣} -> y ∈ Y -> y ∈ TermImage Y
    app : (𝓸 : ∣ S ∣) (𝒕 : ⟦ S ⟧ 𝓸 -> ∣ 𝑨 ∣)
      ->  (∀ i -> 𝒕 i ∈ TermImage Y)
         -------------------------------------------
      ->  (⟦ 𝑨 ⟧ 𝓸 𝒕) ∈ TermImage Y

  --1. TermImage is a subuniverse
  TermImageIsSub : (Y : Pred ∣ 𝑨 ∣ k) → TermImage Y ∈ Subuniverses 𝑨
  TermImageIsSub Y  = λ 𝓸 𝒂 x → app 𝓸 𝒂 x
  -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

  --2. Y ⊆ TermImageY
  Y⊆TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ k) -> Y ⊆ TermImage Y
  Y⊆TermImageY {x} Y {a} a∈Y = var a∈Y
  -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)
  
  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y
  --    Proof: see `sgIsSmallest`

  --Finally, we can prove the desired inclusion.
  SgY⊆TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ k) -> Sg Y ⊆ TermImage Y
  SgY⊆TermImageY {x} Y = sgIsSmallest (TermImageIsSub Y) (Y⊆TermImageY{x} Y)

  -- Now we should be able to prove something like the following
  -- (if we wanted to bother generalizing the relation ≃ to predicates):
  -- SgY≃TermImageY : (Y : Pred ∣ 𝑨 ∣ k) ->  (TermImage Y) ≃ (Sg Y)
  -- SgY≃TermImageY {x} Y = ? 
