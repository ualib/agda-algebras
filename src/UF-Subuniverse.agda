--File: UF-Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 26 Apr 2020
--Notes: Based on the file `Subuniverse.agda`

{-# OPTIONS --without-K --exact-split --safe #-}   -- allow-unsolved-metas #-}

open import UF-Prelude
open import UF-Basic
open import UF-Free
open import UF-Hom
open import Relation.Unary using (Pred; _∈_; _⊆_; ⋂; ⋃)
open import Data.Product  renaming (_,_ to _؛_) using (∃) -- ; _,_; _×_;Σ-syntax) public renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)
--open import UF-Extensionality
--open import UF-Truncation

module UF-Subuniverse {S : Signature 𝓞 𝓥} where

Subuniverses : (A : Algebra 𝓤 S)  →   Pred (Pred ∣ A ∣ 𝓡)  _  -- (i ⊔ j ⊔ ℓ₁ ⊔ ℓ₂)
Subuniverses A B =  (𝓸 : ∣ S ∣ ) → (𝒂 : ∥ S ∥ 𝓸 → ∣ A ∣ ) →  Im 𝒂 ⊆ B → ∥ A ∥ 𝓸 𝒂 ∈ B

-- To keep A at same universe level as ∃ B , 𝐹ᴮ, force B to live in the same universe.
-- We need to do this so that both A and ∃ B , 𝐹ᴮ can be classified by the same predicate SClo

module _ {𝑨 𝑩 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤 }{𝐹 : (𝓸 : ∣ S ∣) → Op (∥ S ∥ 𝓸) (∃ B)} where
  data A-is-supalgebra-of_  : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
    mem :  {𝑩 : Algebra 𝓤 S}
     →     ( ∀{𝓸 : ∣ S ∣ } { x : ∥ S ∥ 𝓸 → ∃ B }
     →     ∣ 𝐹 𝓸 x ∣ ≡ ∥ 𝑨 ∥ 𝓸 ( λ i → ∣ x i ∣ ) )
     →     𝑩 ≡ ( ∃ B , 𝐹 ) → A-is-supalgebra-of 𝑩

  _is-subalgebra-of-A : Algebra 𝓤 S → _ ̇
  𝑩 is-subalgebra-of-A = A-is-supalgebra-of 𝑩

  is-supalgebra-elim : A-is-supalgebra-of (∃ B , 𝐹)  →  𝑩 ≡ ( ∃ B , 𝐹 )
   →                       ( ∀(𝓸 : ∣ S ∣ ) ( x : ∥ S ∥ 𝓸 → ∃ B )
                            ------------------------------------------
   →                       ∣ 𝐹 𝓸 x ∣ ≡ ∥ 𝑨 ∥ 𝓸 ( λ i → ∣ x i ∣) )

  is-supalgebra-elim (mem .{(∃ B , 𝐹)} eq1 _ ) _ 𝓸 x = eq1

  subalg-closure : A-is-supalgebra-of (∃ B , 𝐹)
   →                  ∀ ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ )
   →                  ( Im 𝒂 ⊆ B )
   →                  ∥ 𝑨 ∥ 𝓸 𝒂 ∈ B
  subalg-closure ( mem .{ ( ∃ B , 𝐹 ) } eq1 eq2 ) 𝓸 𝒂 Im𝒂⊆B =
    let eq1app = eq1{𝓸}{λ i  →  𝒂 i , Im𝒂⊆B i } in
    let Aval = ∥ 𝑨 ∥ 𝓸 𝒂 in
    let Fval = ∣ 𝐹 𝓸 (λ i₁ → 𝒂 i₁ , Im𝒂⊆B i₁) ∣ in
    let Fval∈B = ∥ 𝐹 𝓸 (λ i₁ → 𝒂 i₁ , Im𝒂⊆B i₁) ∥ in 
      cong-pred{A = ∣ 𝑨 ∣}{B = B} Fval Aval Fval∈B eq1app

  subalg-to-subuniv : _is-subalgebra-of-A ( ∃ B , 𝐹 )
   →                       B ∈ Subuniverses 𝑨
  subalg-to-subuniv BF≤A 𝓸 𝒂 Im𝒂∈B = subalg-closure BF≤A 𝓸 𝒂 Im𝒂∈B

  -- Subuniverses are closed under the action of term operations.
  sub-term-closed : {X : 𝓤 ̇} → B ∈ Subuniverses 𝑨 → ( 𝒕 : Term )
   →                      ( 𝒙 : X → ∣ 𝑨 ∣ )   →    ( ∀ i → 𝒙 i ∈ B )
                           -------------------------------------------
   →                        ( (𝒕 ̇ 𝑨) 𝒙 ) ∈ B
  sub-term-closed P≤𝑨 ( generator x ) 𝒙 𝒙∈P = 𝒙∈P x
  sub-term-closed P≤𝑨 ( node 𝓸 𝒕 ) 𝒙 𝒙∈P =
    P≤𝑨 𝓸 (λ z → (𝒕 z ̇ 𝑨) 𝒙) (λ x → sub-term-closed P≤𝑨 (𝒕 x) 𝒙 𝒙∈P)

  -- interp-sub : {X : 𝓤 ̇} →  ( sub : ( ∃ B , 𝐹 ) is-subalgebra-of-A ) → 𝑩 ≡ (∃ B , 𝐹)
  --  →            ( p : Term )  (𝒙  : X → ∣ 𝑨 ∣ )  ( Imx⊆B : Im 𝒙 ⊆ B )
  --               ------------------------------------------------------------------------------------------
  --  →            ( p ̇ (∃ B , 𝐹) )  ( img 𝒙 B Imx⊆B ) ≡  ( ( p ̇ 𝑨 ) 𝒙 , sub-term-closed (subalg-to-subuniv sub) p 𝒙 Imx⊆B )
  -- interp-sub sub eq0 (generator x) 𝒙 Imx⊆B = refl
  -- interp-sub sub eq0 (node 𝓸 𝒕) 𝒙 Imx⊆B  = {!!}

record Subuniverse {𝑨 : Algebra 𝓤 S} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇ where
  constructor mksub
  field
    sset  : Pred ∣ 𝑨 ∣ 𝓤
    isSub : sset ∈ Subuniverses 𝑨


module _ {𝑨 : Algebra 𝓤 S}{𝑩 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤} {𝐹 : (𝓸 : ∣ S ∣) → Op ( ∥ S ∥ 𝓸 ) ( ∃ B ) }
  {X : 𝓤 ̇ } ( B∈SubA : B ∈ Subuniverses 𝑨 ) where

  SubunivAlg : Algebra 𝓤 S
  SubunivAlg = ∃ B , λ 𝓸 x → ∥ 𝑨 ∥ 𝓸 ( ∣_∣ ∘ x ) , B∈SubA 𝓸 ( ∣_∣ ∘ x ) ( ∥_∥ ∘ x )

  subuniv-to-subalg : _is-subalgebra-of-A{𝓤}{𝑨 = 𝑨}{ 𝑩 = SubunivAlg } SubunivAlg
  subuniv-to-subalg = mem (λ{𝓸}{x} -> refl) refl


data Sg  { 𝑨 : Algebra 𝓤 S } ( X : Pred ∣ 𝑨 ∣ 𝓤 ) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {v} → v ∈ X → v ∈ Sg X
  app :  (𝓸 : ∣ S ∣) {𝒂 : ∥ S ∥ 𝓸 -> ∣ 𝑨 ∣ }
    →   Im 𝒂 ⊆ Sg{𝑨} X
    ------------------
    → ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Sg X

sgIsSub : {𝑨 : Algebra 𝓤 S} ( X : Pred ∣ 𝑨 ∣ 𝓤 ) → Sg X ∈ Subuniverses 𝑨
sgIsSub _ 𝓸 𝒂 α = app 𝓸 α

-- WARNING: if you move X into the scope of sgIsSmallest, you get the following error:
-- "An internal error has occurred. Please report this as a bug.
--  Location of the error: src/full/Agda/TypeChecking/Monad/Context.hs:119"
-- I think it has to do with variable generalization.

sgIsSmallest : { 𝑨 : Algebra 𝓤 S } { Y : Pred ∣ 𝑨 ∣ ( 𝓞 ⊔ 𝓥 ⊔ 𝓤 ) } { X : Pred ∣ 𝑨 ∣ 𝓤 }
 →               Y ∈ Subuniverses 𝑨  →  X ⊆ Y
                  ------------------------------
 →                            Sg X ⊆ Y

-- By induction on x ∈ Sg X, show x ∈ Y
sgIsSmallest { 𝑨 = 𝑨 } { Y = Y } { X = X }  Y∈Sub𝑨 X⊆Y (var v∈X) = X⊆Y v∈X
sgIsSmallest { 𝑨 = 𝑨 } { Y = Y} YIsSub X⊆Y (app 𝓸 {𝒂} im𝒂⊆SgX) = app∈Y where
  -- First, show the args are in Y
  im𝒂⊆Y : Im 𝒂 ⊆ Y
  im𝒂⊆Y i = sgIsSmallest YIsSub X⊆Y (im𝒂⊆SgX i)

  -- Since Y is a subuniverse of 𝑨, it contains the application of 𝓸 to said args
  app∈Y : ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Y
  app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y

-- Same issue here as above
-- Obs 2.5. Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.
--module _ {𝑨 : Algebra k S} 
sub-inter-is-sub : {𝑨 : Algebra 𝓤 S} { I : 𝓤 ̇ } { 𝔄 : I → Pred ∣ 𝑨 ∣ ( 𝓞 ⊔ 𝓥 ⊔ 𝓤 ) }
 →                   ( ( i : I ) → 𝔄 i ∈ Subuniverses 𝑨 ) → ⋂ I 𝔄 ∈ Subuniverses 𝑨
sub-inter-is-sub { 𝑨 = 𝑨 } { I = I } { 𝔄 = 𝔄 } 𝔄i∈Sub𝑨 𝓸 𝒂 im𝒂⊆⋂A = α where
    α : ∥ 𝑨 ∥ 𝓸 𝒂 ∈ ⋂ I 𝔄
    -- Suffices to show (i : I) → ∥ A ∥ 𝓸 𝒂 ∈ A i, which is immediate since A i is a subuniverse)
    α i = 𝔄i∈Sub𝑨 i 𝓸 𝒂 λ j → im𝒂⊆⋂A j i

-- Hom is subuniverse
HomImage :  {𝑨 : Algebra 𝓤 S} {𝑩 : Algebra 𝓤 S} (f : Hom 𝑨 𝑩)  →  Pred ∣ 𝑩 ∣ _
HomImage f = λ b → Image_∋_ ? ? -- {𝓤 = 𝓤} { 𝓦 = 𝓞 ⊔ 𝓥 ⊔ 𝓤 } ∣ f ∣ b

hom-image-is-sub : { 𝑨 : Algebra 𝓤 S } { 𝑩 : Algebra ( 𝓞 ⊔ 𝓥 ⊔ 𝓤 ) S }
 →                      ( f : Hom 𝑨 𝑩 )
                         ---------------------------------------
 →                    HomImage { 𝑨 } { 𝑩 } f ∈ Subuniverses 𝑩
hom-image-is-sub {𝑨} {𝑩} f 𝓸 𝒃 𝒃∈Imf =
  let 𝒂 = λ x -> Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) in
  -- let 𝒃≡𝒄 = ∀-extensionality-ℓ₁-ℓ₂ (λ x → InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)) in 
  -- let fin = trans (∥ f ∥ 𝓸 𝒂) (cong ( ∥ 𝑩 ∥ 𝓸 ) 𝒃≡𝒄) in
    eq (∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x)) ( ∥ 𝑨 ∥ 𝓸 𝒂) ? -- (sym fin)


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

data TermImage  {𝑨 : Algebra 𝓤 S} (Y : Pred ∣ 𝑨 ∣ 𝓤) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {y : ∣ 𝑨 ∣}  →  y ∈ Y  →  y ∈ TermImage Y
  app : (𝓸 : ∣ S ∣) (𝒕 : ∥ S ∥ 𝓸  →  ∣ 𝑨 ∣)
    →   (∀ i  →  𝒕 i ∈ TermImage {𝑨} Y)
       ------------------------------
    →   ( ∥ 𝑨 ∥ 𝓸 𝒕 ) ∈ TermImage Y

--1. TermImage is a subuniverse
TermImageIsSub : {𝑨 : Algebra 𝓤 S} ( Y : Pred ∣ 𝑨 ∣ 𝓤 ) → TermImage Y ∈ Subuniverses 𝑨
TermImageIsSub Y  = λ 𝓸 𝒂 x → app 𝓸 𝒂 x
-- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

--2. Y ⊆ TermImageY
Y⊆TermImageY :  {X : 𝓤 ̇} {x : X} {𝑨 : Algebra 𝓤 S}  →  ( Y : Pred ∣ 𝑨 ∣ 𝓤 )  →  Y ⊆ TermImage {𝑨} Y
Y⊆TermImageY {x = x} Y {a} a∈Y = var a∈Y
-- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

-- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y
--    Proof: see `sgIsSmallest`

--Finally, we can prove the desired inclusion.
SgY⊆TermImageY :  { X : 𝓤 ̇ } {x : X} {𝑨 : Algebra 𝓤 S}  →  (Y : Pred ∣ 𝑨 ∣ 𝓤)  →  Sg{𝑨 = 𝑨} Y ⊆ TermImage Y
SgY⊆TermImageY {x = x} Y = sgIsSmallest (TermImageIsSub Y) (Y⊆TermImageY{x = x} Y)

  -- Now we should be able to prove something like the following
  -- (if we wanted to bother generalizing the relation ≃ to predicates):
  -- SgY≃TermImageY : (Y : Pred ∣ 𝑨 ∣ k) ->  (TermImage Y) ≃ (Sg Y)
  -- SgY≃TermImageY {x} Y = ? 
