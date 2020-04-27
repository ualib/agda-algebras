--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 26 Feb 2020
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-} --allow-unsolved-metas #-}

open import UF-Prelude using (𝓘; 𝓜; 𝓞; 𝓡; 𝓢; 𝓣; 𝓤; 𝓥; _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; _≡_; refl; _≡⟨_⟩_; _∎; ap; _⁻¹; _∘_; Pred; _⊆_; _∈_; Image_∋_; Im_⊆_; Inv; InvIsInv; eq)

open import UF-Basic using (Signature; Algebra; Op)
open import UF-Free using (Term; _̇_; _̂_; generator; node)
open import UF-Hom using (Hom)
open import UF-Rel using (Transitive)
open import UF-Extensionality using (funext)

open import Relation.Unary using (⋂)

module UF-Subuniverse {S : Signature 𝓞 𝓥} where

Subuniverses : (𝑨 : Algebra 𝓤 S) → Pred (Pred ∣ 𝑨 ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)
Subuniverses 𝑨 B = (𝓸 : ∣ S ∣) (𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ ) → Im 𝒂 ⊆ B → ∥ 𝑨 ∥ 𝓸 𝒂 ∈ B

-- To keep A at same universe level as ∃ P , B, force P to live in the same universe
-- We need to do this so that both A and ∃ P , B can be classified by the same predicate SClo
data _is-supalgebra-of_ (A : Algebra 𝓤 S) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  mem : {B : Pred ∣ A ∣ 𝓤}   {𝐹 : ( 𝓸 : ∣ S ∣ ) → Op ( ∥ S ∥ 𝓸 ) (Σ B)} 
    →  ( ( 𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → Σ B) → ∣ 𝐹 𝓸 𝒂 ∣ ≡ ∥ A ∥ 𝓸 (λ i → ∣ 𝒂 i ∣ ) ) →
        A is-supalgebra-of (Σ B , 𝐹)

-- is-supalgebra-of-elim : (𝑩 : Algebra 𝓤 S) (B : Pred ∣ 𝑨 ∣ 𝓤) ( 𝐹 : (𝓸 : ∣ S ∣ ) → Op (∥ S ∥ 𝓸) (∃ B))
--   →                    𝑩 ≡ (∃ B , 𝐹)  → 𝑨 is-supalgebra-of (∃ B , 𝐹)
--   →                    ( ( 𝓸 : ∣ S ∣ ) → ( 𝒂 : ∥ S ∥ 𝓸 → ∃ B) → ∣ 𝐹 𝓸 𝒂 ∣ ≡ ∥ 𝑨 ∥ 𝓸 (λ i → ∣ 𝒂 i ∣ ) )
-- is-supalgebra-of-elim 𝑩 p b .(𝑩 ≡ (∃ p , b)) (mem .(∃ p , b) eq1 eq2) 𝓸 x = ?

_is-subalgebra-of_ : Algebra 𝓤 S → Algebra 𝓤 S → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
B is-subalgebra-of A = A is-supalgebra-of B

module _ {𝑨 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤}
  {𝐹 : ( 𝓸 : ∣ S ∣ ) → Op ( ∥ S ∥ 𝓸 ) (Σ B)}
  ( B∈SubA : B ∈ Subuniverses 𝑨) where

  SubunivAlg : Algebra 𝓤 S
  SubunivAlg = Σ B , λ 𝓸 x → ∥ 𝑨 ∥ 𝓸 ( ∣_∣ ∘ x ) , B∈SubA 𝓸 ( ∣_∣ ∘ x ) (∥_∥ ∘ x)

  subuniv-to-subalg : SubunivAlg is-subalgebra-of 𝑨
  subuniv-to-subalg = mem {B = B} {𝐹 = ∥ SubunivAlg ∥ } λ 𝓸 𝒂 → refl _
  --    mem {B = B} {𝐹 = ∥ SubunivAlg ∥}   ( Σ B , ∥ SubunivAlg ∥ ) {!!} -- refl _ (λ 𝓸 x -> refl _)  --

record Subuniverse  {𝑨 : Algebra 𝓤 S} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ where
  constructor mksub
  field
    sset  : Pred ∣ 𝑨 ∣ 𝓤
    isSub : sset ∈ Subuniverses 𝑨

module _ {𝑨 : Algebra 𝓤 S} where
  data Sg (X : Pred ∣ 𝑨 ∣ 𝓣) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣) where
    var : ∀ {v} → v ∈ X → v ∈ Sg X
    app :  ( 𝓸 : ∣ S ∣ ) { 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ }
      →       Im 𝒂 ⊆ Sg X
               ---------------
      →       ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Sg X

  sgIsSub : ( X : Pred ∣ 𝑨 ∣ 𝓤 ) → Sg X ∈ Subuniverses 𝑨
  sgIsSub _ 𝓸 𝒂 α = app 𝓸 α

  -- postulate hom-sg-to-fun : {S : Signature 𝓞 𝓥} {𝑨 : Algebra 𝓤 S} {𝑩 : Algebra 𝓤 S} {X : Pred ∣ 𝑨 ∣ 𝓤}
  --  → Hom (SubunivAlg {S = S} {𝑨} {B = Sg X} (sgIsSub ?)) 𝑩 → (∃ X → ∣ 𝑩 ∣)
  -- hom-sg-to-fun = {!!}

  -- WARNING: if you move X into the scope of sgIsSmallest, you get the following error:
  -- "An internal error has occurred. Please report this as a bug.
  --  Location of the error: src/full/Agda/TypeChecking/Monad/Context.hs:119"
  -- I think it has to do with variable generalization
  --module _ where
  sgIsSmallest : { X : Pred ∣ 𝑨 ∣ 𝓡  } {Y : Pred ∣ 𝑨 ∣ 𝓢 }
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
    app∈Y : ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Y
    app∈Y = YIsSub 𝓸 𝒂 im𝒂⊆Y

-- -- Same issue here as above
-- -- Obs 2.5. Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨.
module _ {𝑨 : Algebra 𝓤 S}  {I : 𝓘 ̇} {A : I → Pred ∣ 𝑨 ∣ 𝓣} where
  sub-inter-is-sub : ( (i : I) → A i ∈ Subuniverses 𝑨) → ⋂ I A ∈ Subuniverses 𝑨
  sub-inter-is-sub Ai-is-Sub 𝓸 𝒂 im𝒂⊆⋂A = α where
    α : ∥ 𝑨 ∥ 𝓸 𝒂 ∈ ⋂ I A      -- Suffices to show (i : I) → ⟦ A ⟧ 𝓸 𝒂 ∈ A i
    α i = Ai-is-Sub i 𝓸 𝒂 λ j → im𝒂⊆⋂A j i    -- Immediate from A i being a subuniverse

-- Hom is subuniverse

module _ {𝑨 𝑩 : Algebra 𝓤 S} (f : Hom 𝑨 𝑩) where
  HomImage : ∣ 𝑩 ∣ → 𝓤 ̇
  HomImage = λ b → Image ∣ f ∣ ∋ b

  hom-image-is-sub : funext 𝓥 𝓤 → HomImage ∈ Subuniverses 𝑩
  hom-image-is-sub fe 𝓸 𝒃 𝒃∈Imf =
    eq (∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x)) ( ∥ 𝑨 ∥ 𝓸 ar) γ
    where
     ar : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣
     ar = λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)

     ζ = fe (λ x → InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) )

     γ : ∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x) ≡ ∣ f ∣ (∥ 𝑨 ∥ 𝓸 (λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)))
     γ =   ∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x)       ≡⟨ ap (λ - → ∥ 𝑩 ∥ 𝓸 - ) ζ ⁻¹ ⟩
            ( ∥ 𝑩 ∥ 𝓸 ) ( ∣ f ∣ ∘ ar )     ≡⟨ ( ∥ f ∥ 𝓸 ar ) ⁻¹ ⟩
             ∣ f ∣ ( ∥ 𝑨 ∥ 𝓸 ar )          ∎

  -- Paper-pencil-proof.
  -- Let 𝓸 be an op symbol.  Let args : ∥ S ∥ 𝓸 → ∣ 𝑩 ∣ be a (∥ S ∥ 𝓸)-tuple of elements ∣ 𝑩 ∣.
  -- Assume ∀ i₁ → args i₁ ∈ Image ∣ f ∣.  We must show (∥ 𝑩 ∥ 𝓸) args ∈ Image ∣ f ∣.
  -- ∀ i₁ → args i₁ ∈ Image ∣ f ∣ implies  ∃ 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ such that ∣ f ∣ ∘ 𝒂 = args.
  -- i.e., ∀ i₁ ->  ∣ f ∣ 𝒂 i₁ = args i₁.  Since f : Hom 𝑨 𝑩, we have
  -- (∥ 𝑩 ∥ 𝓸) args = (∥ 𝑩 ∥ 𝓸) (∣ f ∣ ∘ 𝒂) = ∣ f ∣ ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Image ∣ f ∣

module _  {𝑨 𝑩 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤} (X Y : 𝓤 ̇)  where

  -- Obs 2.11 (on subuniverse generation as image of terms). If Y is a subset of A, then
  --   Sg^{𝑨}(Y) = { t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: Fin(ρ t) -> Y }.
  -- Paper-pencil-proof.
  --   Induction on the height of t shows that every subuniverse is closed under the action of t^𝑨. Thus the right-hand
  --   side is contained in the left. On the other hand, the right-hand side is a subuniverse that contains the elements
  --   of Y (take t = x₁), so it contains Sg^{𝑨}(Y), as the latter is the smallest subuniverse containing Y. ☐

  -- To prove Obs 2.11, we first prove the following usefull lemma:

  -- Subuniverses are closed under the action of term operations.
  sub-term-closed : B ∈ Subuniverses 𝑨 → ( 𝒕 : Term ) → ( 𝒃 : X → ∣ 𝑨 ∣ ) → ( ∀ i → 𝒃 i ∈ B )
   →                         ( (𝒕 ̇ 𝑨) 𝒃 ) ∈ B
  sub-term-closed B≤𝑨 (generator x) 𝒃 𝒃∈B = 𝒃∈B x
  sub-term-closed B≤𝑨 (node 𝓸 𝒕) 𝒃 𝒃∈B =
    B≤𝑨 𝓸 (λ z → (𝒕 z ̇ 𝑨) 𝒃) (λ x → sub-term-closed B≤𝑨 (𝒕 x) 𝒃 𝒃∈B)
     -- (this proof was found automatically by C-c C-a)

  -- sub-term-closed proves Sg^𝑨(Y) ⊇ { t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: Fin(ρ t) -> Y } := ImageTerms
  -- Next we prove Sg^{𝑨}(Y) ⊆ { t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: Fin(ρ t) -> Y }, as follows:
  -- 1. The image of Y under all terms, which we call `TermImage Y`, is a subuniverse of 𝑨; ie, TermImageY = ⋃{𝒕:Term} Image (𝒕 ̇ 𝑨) ≤ 𝑨.
  -- 2. Y ⊆ TermImageY (obvious)
  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y (see `sgIsSmallest`) so Sg^𝑨(Y) ⊆ TermImageY ∎
  data TermImage ( Y : Pred ∣ 𝑨 ∣ 𝓤 ) : Pred ∣ 𝑨 ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤)  where
    var : ∀ {y : ∣ 𝑨 ∣} → y ∈ Y → y ∈ TermImage Y
    app :   ( 𝓸 : ∣ S ∣ ) ( 𝒕 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ )
     →    ( ∀ i  →  𝒕 i ∈ TermImage Y )
           -------------------------------
     →     ( ∥ 𝑨 ∥ 𝓸 𝒕 ) ∈ TermImage Y

  --1. TermImage is a subuniverse
  TermImageIsSub : (Y : Pred ∣ 𝑨 ∣ 𝓤) → TermImage Y ∈ Subuniverses 𝑨
  TermImageIsSub Y  = λ 𝓸 𝒂 x → app 𝓸 𝒂 x
  -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

  --2. Y ⊆ TermImageY
  Y⊆TermImageY : {x : X} -> (Y : Pred ∣ 𝑨 ∣ 𝓤) -> Y ⊆ TermImage Y
  Y⊆TermImageY {x} Y {a} a∈Y = var a∈Y
  -- AUTOMATION WORKS! (this proof was found automatically by C-c C-a)

  -- 3. Sg^𝑨(Y) is the smallest subuniverse containing Y
  --    Proof: see `sgIsSmallest`

  --Finally, we can prove the desired inclusion.
  SgY⊆TermImageY : {x : X} → (Y : Pred ∣ 𝑨 ∣ 𝓤) → Sg Y ⊆ TermImage Y
  SgY⊆TermImageY {x} Y = sgIsSmallest (TermImageIsSub Y) (Y⊆TermImageY{x} Y)

  -- Now we should be able to prove something like the following
  -- (if we could be bothered to generalize the relation ≃ to predicates):
  -- SgY≃TermImageY : (Y : Pred ∣ 𝑨 ∣ k) ->  (TermImage Y) ≃ (Sg Y)
  -- SgY≃TermImageY {x} Y = ? 




