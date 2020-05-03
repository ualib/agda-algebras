--File: Subuniverse.agda
--Author: William DeMeo and Siva Somayyajula
--Date: 20 Feb 2020
--Updated: 26 Feb 2020
--Notes: Based on the file `subuniverse.agda` (10 Jan 2020).

{-# OPTIONS --without-K --exact-split --safe #-} --allow-unsolved-metas #-}

open import UF-Prelude using (Universe; 𝓘; 𝓜; 𝓞; 𝓡; 𝓢; 𝓣; 𝓤; 𝓥; 𝓦;  _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; _≡_; refl; _≡⟨_⟩_; _∎; ap; _⁻¹; _∘_; Pred; _×_; _⊆_; _∈_; Image_∋_; Im_⊆_; Inv; InvIsInv; eq; im; pr₁; transport; codomain; domain)

open import UF-Basic using (Signature; Algebra; Op)
open import UF-Free using (Term; _̇_; _̂_; generator; node; comm-hom-term)
open import UF-Hom using (Hom)
open import UF-Rel using (Transitive)
open import UF-Extensionality using (funext; global-funext; dfunext; global-dfunext)

open import Relation.Unary using (⋂)

module UF-Subuniverse {S : Signature 𝓞 𝓥} where

Subuniverses : (𝑨 : Algebra 𝓤 S) → Pred (Pred ∣ 𝑨 ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)
Subuniverses (A , Fᴬ) B = ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → A ) → Im 𝒂 ⊆ B → Fᴬ 𝓸 𝒂 ∈ B

-- To keep A at same universe level as Σ B , 𝐹 , force B to live in the same universe.
-- We need to do this so that both A and Σ B , 𝐹 can be classified by the same predicate SClo.
data _is-supalgebra-of_ (𝑨 : Algebra 𝓤 S) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  mem :   {B : Pred ∣ 𝑨 ∣ 𝓤}  { 𝐹 : ( 𝓸 : ∣ S ∣ ) → Op ( ∥ S ∥ 𝓸 ) (Σ B) }
    →    ( ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸 → Σ B )  →  ∣ 𝐹 𝓸 𝒂 ∣ ≡ ∥ 𝑨 ∥ 𝓸 (λ i → ∣ 𝒂 i ∣ ) )
    →    𝑨 is-supalgebra-of (Σ B , 𝐹)

_is-subalgebra-of_ : Algebra 𝓤 S → Algebra 𝓤 S → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
B is-subalgebra-of A = A is-supalgebra-of B


--------------------------------
-- Elimination rule for sub/supalgebra.
-- For some reason, I'm able to get an elimination rule only for `A-is-supalgebra-of_` for fixed A.  (todo: try to fix this)
module _
  {𝑨 : Algebra 𝓤 S}
  {𝑩 : Algebra 𝓤 S}
  {B : Pred ∣ 𝑨 ∣ 𝓤}
  { 𝐹 : (𝓸 : ∣ S ∣) → Op (∥ S ∥ 𝓸) ( Σ B ) }   where

  data A-is-supalgebra-of_  : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
    mem :  {𝑩 : Algebra 𝓤 S}
      →    ( {𝓸 : ∣ S ∣ } { x : ∥ S ∥ 𝓸 → Σ B}  →  ∣ 𝐹 𝓸 x ∣ ≡ ∥ 𝑨 ∥ 𝓸 ( λ i → ∣ x i ∣ ) )
      →    𝑩 ≡ ( Σ B , 𝐹 ) → A-is-supalgebra-of 𝑩

  _is-subalgebra-of-A : Algebra 𝓤 S  →  _ ̇
  𝑩 is-subalgebra-of-A = A-is-supalgebra-of 𝑩

  is-supalgebra-elim : A-is-supalgebra-of ( Σ B , 𝐹 )
    →                 𝑩 ≡ ( Σ B , 𝐹 )    → ( ∀ ( 𝓸 : ∣ S ∣ ) ( x : ∥ S ∥ 𝓸 → Σ B )
    →                 ∣ 𝐹 𝓸 x ∣ ≡ ∥ 𝑨 ∥ 𝓸 ( λ i → ∣ x i ∣ ) )
  is-supalgebra-elim (mem .{(Σ B , 𝐹)} eq1 _ ) _ 𝓸 x = eq1


module _ {𝑨 : Algebra 𝓤 S} {B : Pred ∣ 𝑨 ∣ 𝓤}
  {𝐹 : ( 𝓸 : ∣ S ∣ ) → Op ( ∥ S ∥ 𝓸 ) (Σ B)}
  ( B∈SubA : B ∈ Subuniverses 𝑨) where

  SubunivAlg : Algebra 𝓤 S
  SubunivAlg = Σ B , λ 𝓸 x → ∥ 𝑨 ∥ 𝓸 ( ∣_∣ ∘ x ) , B∈SubA 𝓸 ( ∣_∣ ∘ x ) (∥_∥ ∘ x)

  subuniv-to-subalg : SubunivAlg is-subalgebra-of 𝑨
  subuniv-to-subalg = mem {B = B} { 𝐹 = ∥ SubunivAlg ∥ } λ 𝓸 𝒂 → refl _
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

module _ {𝑨 𝑩 : Algebra 𝓤 S} (f : Hom 𝑨 𝑩)  where
  HomImage : ∣ 𝑩 ∣ → 𝓤 ̇
  HomImage = λ b → Image ∣ f ∣ ∋ b

  -- hom-image : 𝓤 ̇
  -- hom-image = Σ b ꞉ ∣ 𝑩 ∣ , Image ∣ f ∣ ∋ b

  hom-image : 𝓤 ̇
  hom-image = Σ (Image_∋_ ∣ f ∣)

  fres : ∣ 𝑨 ∣ → Σ (Image_∋_ ∣ f ∣)
  fres a = ∣ f ∣ a , im a

  hom-image-alg : Algebra 𝓤 S
  hom-image-alg = hom-image , ops-interp
   where
    𝒂 : {𝓸 : ∣ S ∣ } ( x : ∥ S ∥ 𝓸 → hom-image ) (y : ∥ S ∥ 𝓸)   →   ∣ 𝑨 ∣
    𝒂 x y = Inv ∣ f ∣  ∣ x y ∣ ∥ x y ∥

    ops-interp : ( 𝓸 : ∣ S ∣ ) → Op (∥ S ∥ 𝓸) hom-image
    ops-interp = λ 𝓸 x →( ∣ f ∣  ( ∥ 𝑨 ∥ 𝓸 (𝒂 x) ) , im ( ∥ 𝑨 ∥ 𝓸 (𝒂 x) ) )

  hom-image-is-sub : {funext 𝓥 𝓤} → HomImage ∈ Subuniverses 𝑩
  hom-image-is-sub {fe} 𝓸 𝒃 𝒃∈Imf =
    eq (∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x)) ( ∥ 𝑨 ∥ 𝓸 ar) γ
    where
     ar : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣
     ar = λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)

     ζ = fe (λ x → InvIsInv ∣ f ∣ (𝒃 x) (𝒃∈Imf x) )

     γ : ∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x) ≡ ∣ f ∣ (∥ 𝑨 ∥ 𝓸 (λ x → Inv ∣ f ∣ (𝒃 x) (𝒃∈Imf x)))
     γ =   ∥ 𝑩 ∥ 𝓸 (λ x → 𝒃 x)       ≡⟨ ap ( ∥ 𝑩 ∥ 𝓸 ) ζ ⁻¹ ⟩
            ( ∥ 𝑩 ∥ 𝓸 ) ( ∣ f ∣ ∘ ar )     ≡⟨ ( ∥ f ∥ 𝓸 ar ) ⁻¹ ⟩
             ∣ f ∣ ( ∥ 𝑨 ∥ 𝓸 ar )          ∎

  -- Paper-pencil-proof.
  -- Let 𝓸 be an op symbol.  Let args : ∥ S ∥ 𝓸 → ∣ 𝑩 ∣ be a (∥ S ∥ 𝓸)-tuple of elements ∣ 𝑩 ∣.
  -- Assume ∀ i₁ → args i₁ ∈ Image ∣ f ∣.  We must show (∥ 𝑩 ∥ 𝓸) args ∈ Image ∣ f ∣.
  -- ∀ i₁ → args i₁ ∈ Image ∣ f ∣ implies  ∃ 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ such that ∣ f ∣ ∘ 𝒂 = args.
  -- i.e., ∀ i₁ ->  ∣ f ∣ 𝒂 i₁ = args i₁.  Since f : Hom 𝑨 𝑩, we have
  -- (∥ 𝑩 ∥ 𝓸) args = (∥ 𝑩 ∥ 𝓸) (∣ f ∣ ∘ 𝒂) = ∣ f ∣ ∥ 𝑨 ∥ 𝓸 𝒂 ∈ Image ∣ f ∣

  finv : {X : 𝓤 ̇ } (𝒃 : X → ∣ hom-image-alg ∣ ) (x : X) → ∣ 𝑨 ∣
  finv = λ 𝒃 x → Inv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥

  -- hom-image-term-interp : {fe : global-dfunext} {X : 𝓤 ̇ } ( p : Term {X = X} ) (𝒃 : X → ∣ hom-image-alg ∣ )
  --   →                            ( p ̇ hom-image-alg ) 𝒃 ≡ ∣ f ∣  ( ( p ̇ 𝑨 ) ( finv 𝒃 ) ) , im ( ( p ̇ 𝑨 ) ( finv 𝒃 ) )

  -- hom-image-term-interp {fe} {X} (generator x) 𝒃 =
  --   let ∣𝒃x∣ = ∣ 𝒃 x ∣ in
  --   let ∥𝒃x∥ = ∥ 𝒃 x ∥ in
  --   let r1 = ∣ f ∣ (finv 𝒃 x) in
  --   let r2 = im ( finv 𝒃 x ) in
  --   let left = InvIsInv ∣ f ∣ ∣ 𝒃 x ∣ ∥ 𝒃 x ∥ in
  --   let fst = ∣ 𝒃 x ∣ ≡⟨ left ⁻¹ ⟩ r1 ∎ in {!!}
  --       -- Goal: 𝒃 x ≡ ∣ f ∣ (finv 𝒃 x) , im (finv 𝒃 x)
  --         --  𝒃 x                                 ≡⟨ refl _ ⟩
  --         -- ∣ 𝒃 x ∣ , ∥ 𝒃 x ∥                    ≡⟨ ap (λ - → - , ∥ 𝒃 x ∥) fst ⟩
  --         -- ∣ f ∣ (finv 𝒃 x) , ∥ 𝒃 x ∥           ≡⟨ ? ⟩
  --         -- ∣ f ∣ (finv 𝒃 x) , im {A = ∣ 𝑨 ∣} {B = ∣ 𝑩 ∣} (finv 𝒃 x)       ∎

  -- hom-image-term-interp {fe}{X} (node 𝓸 𝒕) 𝒃 = {!!}
  --  where
  --   IH : (x : ∥ S ∥ 𝓸)
  --    → ( 𝒕 x ̇ hom-image-alg ) 𝒃  ≡ ∣ f ∣ ( ( 𝒕 x ̇ 𝑨 ) (finv 𝒃) ) , im ((𝒕 x ̇ 𝑨) (finv 𝒃 ) )
  --   IH x = hom-image-term-interp{fe}{X}(𝒕 x) 𝒃

  --   com-hom-𝓸 :  ∣ f ∣ ( (𝓸 ̂ 𝑨) (λ x → (𝒕 x ̇ 𝑨) ( finv 𝒃 ) ) )
  --                        ≡ ( (𝓸 ̂ 𝑩) (λ x → ∣ f ∣ ( (𝒕 x ̇ 𝑨) ( finv 𝒃 ) ) ) )
  --   com-hom-𝓸 = ∥ f ∥ 𝓸 ( λ x → (𝒕 x ̇ 𝑨) ( finv 𝒃 ) )

  --   com-hom-t : (x : ∥ S ∥ 𝓸)
  --    →    ∣ f ∣ ( ( 𝒕 x ̇ 𝑨 ) ( finv 𝒃 ) ) ≡ (𝒕 x ̇ 𝑩) (∣ f ∣ ∘ (finv 𝒃 ) )
  --   com-hom-t x = comm-hom-term fe 𝑨 𝑩 f (𝒕 x) (finv 𝒃)

  --   com-hom-𝓸' : ∣ f ∣ ( (𝓸 ̂ 𝑨) (λ x → (𝒕 x ̇ 𝑨) ( finv 𝒃 ) ) )
  --                         ≡ ( (𝓸 ̂ 𝑩) (λ x → ∣ f ∣ ( (𝒕 x ̇ 𝑨) ( finv 𝒃 ) ) ) )
  --   com-hom-𝓸' = ∥ f ∥ 𝓸 ( λ x → (𝒕 x ̇ 𝑨) ( finv 𝒃 ) )

  --   γ :  (x : ∥ S ∥ 𝓸)
  --    →  ( (𝒕 x ̇ hom-image-alg) 𝒃 ) ≡ ∣ f ∣ ( (𝓸 ̂ 𝑨) (λ x → ( 𝒕 x ̇ 𝑨 ) (finv 𝒃) ) ) ,
  --                                               im ( (𝓸 ̂ 𝑨) ( λ x → ( 𝒕 x ̇ 𝑨 ) (finv 𝒃 ) ) )
  --   γ = 
  --      ( 𝓸 ̂ hom-image-alg ) (λ x → ( 𝒕 x ̇ hom-image-alg ) 𝒃 )  ≡⟨ {!!} ⟩
  --      ( 𝓸 ̂ hom-image-alg ) (λ x → ∣ f ∣ ( ( 𝒕 x ̇ 𝑨 ) (finv 𝒃) )  , im ( (𝒕 x ̇ 𝑨) (finv 𝒃 ) ) ) ≡⟨ {!!} ⟩
  --      ∣ f ∣ ( (𝓸 ̂ 𝑨) (λ x → ( 𝒕 x ̇ 𝑨 ) (finv 𝒃) ) ) ,  im ( (𝓸 ̂ 𝑨) ( λ x → ( 𝒕 x ̇ 𝑨 ) (finv 𝒃 ) ) )   ∎

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




-- fhom    : (𝓸₁ : Σ.x S) (𝒂₁ : Σ.y S 𝓸₁ → Σ.x A) →
-- pr₁ f (Σ.y A 𝓸₁ 𝒂₁) ≡ Σ.y B 𝓸₁ (λ x → pr₁ f (𝒂₁ x))
-- fhom    = ∥ f ∥




      -- φIH : (x : ∥ S ∥ 𝓸) → Id (Σ (Image_∋_ ∣ f ∣)) ((𝒕 x ̇ HIA) 𝒃) (∣ f ∣ ((𝒕 x ̇ A) (𝒂 𝒃)) , im ((𝒕 x ̇ A) (𝒂 𝒃)))
      -- φIH = λ x → φ 𝒃 (𝒕 x)
      --   hypA = cong-app (A⊢p≈q)

    -- φ : ( 𝒃 : X → ∣ HIA ∣ ) (p : Term)
    --  → ( (p ̇ HIA) 𝒃 ) ≡  ∣ f ∣ ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) ) , im ( (p ̇ A) ( λ x → 𝒂 𝒃 x ) )
    -- φ 𝒃 (generator x) =  𝒃 x ≡⟨ {!!} ⟩ ∣ f ∣ (𝒂 𝒃 x) , im (𝒂 𝒃 x) ∎
    -- φ 𝒃 (node 𝓸 𝒕) =
    --  let lhs = (𝓸 ̂ HIA) (λ x → (𝒕 x ̇ HIA) 𝒃) in
    --  let rhs1 = ∣ f ∣ ((𝓸 ̂ A) (λ x → (𝒕 x ̇ A) (𝒂 𝒃))) in
    --  let rhs2 = im ((𝓸 ̂ A) (λ x → (𝒕 x ̇ A) (𝒂 𝒃))) in
    --    lhs ≡⟨ ap (λ - → (𝓸 ̂ HIA) -) (gfe λ x → φIH2 x) ⟩  rhs1 , rhs2 ∎
    --  where
      -- fhom : (a : ∥ S ∥ 𝓸 → ∣ A ∣ )
      --  →    ∣ f ∣ ( (𝓸 ̂ A) a ) ≡ (𝓸 ̂ B) ( ∣ f ∣ ∘ a )
      -- fhom a = ∥ f ∥ 𝓸 a

      -- φIH2 : (x : ∥ S ∥ 𝓸)
      --  → ( 𝒕 x ̇ HIA ) 𝒃  ≡ ∣ f ∣ ( ( 𝒕 x ̇ A ) (𝒂 𝒃) ) , im ((𝒕 x ̇ A) (𝒂 𝒃 ) )
      -- φIH2 x = φ 𝒃 (𝒕 x)

      -- com-hom-𝓸 :  ∣ f ∣ ( (𝓸 ̂ A) (λ x → (𝒕 x ̇ A) ( 𝒂 𝒃 ) ) )
      --                      ≡ ( (𝓸 ̂ B) (λ x → ∣ f ∣ ( (𝒕 x ̇ A) ( 𝒂 𝒃 ) ) ) )
      -- com-hom-𝓸 = ∥ f ∥ 𝓸 ( λ x → (𝒕 x ̇ A) ( 𝒂 𝒃 ) )

      -- com-hom-t : (x : ∥ S ∥ 𝓸)
      --  →    ∣ f ∣ ( ( 𝒕 x ̇ A ) ( 𝒂 𝒃 ) ) ≡ (𝒕 x ̇ B) (∣ f ∣ ∘ (𝒂 𝒃 ) )
      -- com-hom-t x = comm-hom-term gfe A B f (𝒕 x) (𝒂 𝒃)

      -- com-hom-𝓸' : ∣ f ∣ ( (𝓸 ̂ A) (λ x → (𝒕 x ̇ A) ( 𝒂 𝒃 ) ) )
      --                       ≡ ( (𝓸 ̂ B) (λ x → ∣ f ∣ ( (𝒕 x ̇ A) ( 𝒂 𝒃 ) ) ) )
      -- com-hom-𝓸' = ∥ f ∥ 𝓸 ( λ x → (𝒕 x ̇ A) ( 𝒂 𝒃 ) )
