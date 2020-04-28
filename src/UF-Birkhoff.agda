--File: Birkhoff.agda
--AUTHOR: William DeMeo and Siva Somayyajula
--DATE: 23 Feb 2020
--UPDATED: 26 Feb 2020
--NOTATION: see notes at bottom of Preliminaries.agda
--NOTES: Based on the file `birkhoff.agda` (23 Jan 2020).

{-# OPTIONS --without-K --exact-split #-}

open import UF-Prelude using (Universe; 𝓞; 𝓤; 𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; _∘_; _,_; Σ; -Σ; _×_; _≡_; _≡⟨_⟩_; _∎; ap; _⁻¹; Pred; _∈_; _⊆_; ∣_∣; ∥_∥; Epic; EpicInv; cong-app )
open import UF-Basic using (Signature; Algebra; Π')
open import UF-Hom using (Hom)
open import UF-Rel using (ker-pred; Rel)
open import UF-Con using (con; _//_)
open import UF-Subuniverse using (Subuniverse; mksub; Sg; _is-subalgebra-of_; var; app)
open import UF-Extensionality using (funext; global-funext; EInvIsRInv; dfunext)

module UF-Birkhoff  {S : Signature 𝓞 𝓥}  where
-------------------------------------------------------------------------------
--EQUALIZERS
-------------

--...of functions
𝑬 :  {A : 𝓤 ̇ }  {B : 𝓦 ̇ } →  (f g : A → B) → Pred A 𝓦
𝑬 f g x = f x ≡ g x

--..of homs
𝑬𝑯 : {A B : Algebra 𝓤 S} (f g : Hom A B) → Pred ∣ A ∣ 𝓤
𝑬𝑯 f g x = ∣ f ∣ x ≡ ∣ g ∣ x

𝑬𝑯-is-closed : funext 𝓥 𝓤 → {𝓸 : ∣ S ∣ } {𝑨 𝑩 : Algebra 𝓤 S}
              (f g : Hom 𝑨 𝑩)     (𝒂 : ( ∥ S ∥ 𝓸 )  → ∣ 𝑨 ∣ )
 →          ( ( x : ∥ S ∥ 𝓸 ) → ( 𝒂 x ) ∈ ( 𝑬𝑯 {A = 𝑨} {B = 𝑩} f g ) )
            ----------------------------------------
 →          ∣ f ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 ) ≡ ∣ g ∣ ( ∥ 𝑨 ∥ 𝓸 𝒂 )

𝑬𝑯-is-closed fe {𝓸 = 𝓸} {𝑨 = A , Fᴬ} {𝑩 = B , Fᴮ} (f , fhom) (g , ghom) 𝒂 p = 
   f ( Fᴬ 𝓸 𝒂)                     ≡⟨ fhom 𝓸 𝒂 ⟩
   Fᴮ 𝓸 ( λ i  →  f ( 𝒂 i ) )    ≡⟨ ap ( Fᴮ _ ) ( fe p ) ⟩
   Fᴮ 𝓸 ( λ i →  g  ( 𝒂 i ) )    ≡⟨ (ghom 𝓸 𝒂)⁻¹ ⟩
   g ( Fᴬ 𝓸 𝒂)                     ∎

-- Obs 2.1. Equalizer of homs is a subuniverse.
-- Equalizer `𝑬𝑯 f g`  of `f g : Hom 𝑨 𝑩` is a subuniverse of 𝑨.
𝑬𝑯-is-subuniverse :  funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S} (f g : Hom 𝑨 𝑩) → Subuniverse {𝑨 = 𝑨}
𝑬𝑯-is-subuniverse fe {𝑨 = 𝑨} {𝑩 = 𝑩} f g =
  mksub ( 𝑬𝑯 {A = 𝑨}{B = 𝑩} f g ) λ 𝓸 𝒂 x → 𝑬𝑯-is-closed fe {𝑨 = 𝑨} {𝑩 = 𝑩}  f g 𝒂 x 

-------------------------------------------------------------------------------
-- COMPOSITION OF HOMS.
-- Obs 2.0. Composing homs gives a hom.
-- See also: Siva's (infix) def of _>>>_ in the Hom.agda file.
HCompClosed : {𝑨 : Algebra 𝓤 S} {𝑩 : Algebra 𝓦 S} {𝑪 : Algebra 𝓣 S}
 →               Hom 𝑨 𝑩    →    Hom 𝑩 𝑪
                  ---------------------------
 →                          Hom 𝑨 𝑪
HCompClosed {𝑨 = A , FA} {𝑩 = B , FB} { 𝑪 = C , FC } (f , fhom) (g , ghom) = g ∘ f , γ
    where
      γ : ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸  →  A )  →  ( g ∘ f ) ( FA 𝓸 𝒂 ) ≡ FC 𝓸 ( g ∘ f ∘ 𝒂 )
      γ 𝓸 𝒂 = (g ∘ f) (FA 𝓸 𝒂)     ≡⟨ ap g ( fhom 𝓸 𝒂 ) ⟩
                  g (FB 𝓸 (f ∘ 𝒂))     ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
                  FC 𝓸 (g ∘ f ∘ 𝒂)     ∎

-- Obs 2.2. Homs are determined by their values on a generating set (UAFST Ex. 1.4.6.b)
-- If f, g : Hom(𝑨,𝑩), X ⊆ A generates 𝑨, and f|_X = g|_X, then f = g.
-- PROOF.  Suppose the X ⊆ A generates 𝑨 and f|_X = g|_X. Fix an arbitrary a: A.  We show f a = g a.
--         Since X generates 𝑨, ∃ term t (or arity n = ρt, say) and a tuple x: n -> X of generators
--         such that a = t^𝑨 x. Since f|_X = g|_X, f ∘ x = (f x₀, ..., f xₙ) = (g x₀,...,g xₙ) = g ∘ x,
--         so f a = f(t^𝑨 x) = t^𝑩 (f ∘ x) = t^𝑩 (g ∘ x) = g(t^𝑨 x) = g a.     ☐
HomUnique : funext 𝓥 𝓤 → {𝑨 𝑩 : Algebra 𝓤 S}
                ( X : Pred ∣ 𝑨 ∣ 𝓤 )       ( f g : Hom 𝑨 𝑩 )
 →            ( ∀ ( x : ∣ 𝑨 ∣ )  →  x ∈ X  →  ∣ f ∣ x ≡ ∣ g ∣ x )
               -----------------------------------------------------
 →             ( ∀ ( a : ∣ 𝑨 ∣ ) → a ∈ Sg {𝑨 = 𝑨} X → ∣ f ∣ a ≡ ∣ g ∣ a )
HomUnique _ _ _ _ fx≡gx a (var x) = (fx≡gx) a x
HomUnique fe { 𝑨 = A , Fᴬ } { 𝑩 = B , Fᴮ } X (f , fhom) (g , ghom) fx≡gx a ( app 𝓸 {𝒂} im𝒂⊆SgX ) = 
    f ( Fᴬ 𝓸 𝒂)        ≡⟨ fhom 𝓸 𝒂 ⟩
    Fᴮ 𝓸 ( f ∘ 𝒂 )     ≡⟨ ap (Fᴮ 𝓸) (fe induction-hypothesis) ⟩
    Fᴮ 𝓸 ( g ∘ 𝒂)      ≡⟨ ( ghom 𝓸 𝒂 )⁻¹ ⟩
    g ( Fᴬ 𝓸 𝒂 )       ∎
    where induction-hypothesis =
               λ x → HomUnique fe {𝑨 = A , Fᴬ}{𝑩 = B , Fᴮ} X (f , fhom) (g , ghom) fx≡gx (𝒂 x)( im𝒂⊆SgX x )

-- Obs 2.3. If A, B are finite and X generates 𝑨, then |Hom(𝑨, 𝑩)| ≤ |B|^|X|.
-- PROOF. By Obs 2, a hom is uniquely determined by its restriction to a generating set.
--   If X generates 𝑨, then since there are exactly |B|^|X| functions from X to B, the result holds. □

------------------------------------------------------
-- Obs 2.4. Factorization of homs.
-- If f : Hom 𝑨 𝑩, g : Hom 𝑨 𝑪, g epic, Ker g ⊆ Ker f, then ∃ h ∈ Hom 𝑪 𝑩, f = h ∘ g.
--
--        𝑨----f-----> 𝑩
--         \              7
--           \          /
--           g \      / ∃h
--                v  /
--                 𝑪
--
homFactor : funext 𝓤 𝓤
 →           {𝑨 𝑩 𝑪 : Algebra 𝓤 S} (f : Hom 𝑨 𝑩) (g : Hom 𝑨 𝑪)
 →           ker-pred ∣ g ∣ ⊆ ker-pred ∣ f ∣  →   Epic ∣ g ∣
              -------------------------------------------
 →              Σ h ꞉ ( Hom 𝑪 𝑩 ) ,  ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣

--Prove: The diagram above commutes; i.e., ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣
homFactor fe {𝑨 = A , FA } { 𝑩 = B , FB } { 𝑪 = C , FC } (f , fhom) (g , ghom) Kg⊆Kf gEpic =
  ( h , hIsHomCB ) ,  f≡h∘g
  where
    gInv : C → A
    gInv = λ c → (EpicInv g gEpic) c

    h : C → B
    h = λ c → f ( gInv c )

    ξ : (x : A) → ker-pred g (x , gInv (g x))
    ξ x =  ( cong-app (EInvIsRInv fe g gEpic) ( g x ) )⁻¹

    f≡h∘g : f ≡ h ∘ g
    f≡h∘g = fe  λ x → Kg⊆Kf (ξ x)

    ζ : (𝓸 : ∣ S ∣ ) ( 𝒄 : ∥ S ∥ 𝓸 → C ) ( x : ∥ S ∥ 𝓸 ) → 𝒄 x ≡ ( g ∘ gInv ) (𝒄 x)
    ζ 𝓸 𝒄 x = (cong-app (EInvIsRInv fe g gEpic) (𝒄 x))⁻¹

    ι : (𝓸 : ∣ S ∣ )  ( 𝒄 : ∥ S ∥ 𝓸 → C )
         →    (λ x → 𝒄 x) ≡ (λ x → g (gInv (𝒄 x)))
    ι 𝓸 𝒄 = ap (λ - → - ∘ 𝒄) (( EInvIsRInv fe g gEpic )⁻¹)

    useker : (𝓸 : ∣ S ∣ )   ( 𝒄 : ∥ S ∥ 𝓸 → C )
     →       f ( gInv ( g ( FA 𝓸 ( λ x → gInv (𝒄 x) ) ) ) ) ≡ f ( FA 𝓸 ( λ x → gInv (𝒄 x) ) )
    useker = λ 𝓸 𝒄 → Kg⊆Kf ( cong-app (EInvIsRInv fe g gEpic)  ( g ( FA 𝓸 (gInv ∘ 𝒄) ) ) )

    hIsHomCB : (𝓸 : ∣ S ∣ )    ( 𝒂 : ∥ S ∥ 𝓸 → C )
     →          h ( FC 𝓸 𝒂 )  ≡  FB 𝓸 ( λ x → h (𝒂 x) )
    hIsHomCB = λ 𝓸 𝒄 →
      f ( gInv ( FC 𝓸 𝒄 ) )                          ≡⟨ ap (f ∘ gInv) (ap (FC 𝓸) (ι 𝓸 𝒄)) ⟩
      f ( gInv ( FC 𝓸 (  g ∘ ( gInv ∘ 𝒄 ) ) ) )   ≡⟨ ap (λ - → f ( gInv - ) ) ( ghom 𝓸 (gInv ∘ 𝒄)  )⁻¹ ⟩
      f ( gInv ( g ( FA 𝓸 ( gInv ∘ 𝒄 ) ) ) )      ≡⟨ useker 𝓸 𝒄 ⟩
      f ( FA 𝓸 ( gInv ∘ 𝒄 ) )                       ≡⟨ fhom 𝓸 (gInv ∘ 𝒄) ⟩
      FB 𝓸 ( λ x → f ( gInv ( 𝒄 x ) ) )          ∎

-- ---------------------------------------------------------------------------------
-- -- VARIETIES
-- --------------

-- --cf Def 1.10 of Bergman
-- --Let 𝓚 be a class of similar algebras. We write
-- --  H(𝓚) for the class of all homomorphic images of members of 𝓚;
-- --  S(𝓚) for the class of all algebras isomorphic to a subalgebra of a member of 𝓚;
-- --  P(𝓚) for the class of all algebras isomorphic to a direct product of members of 𝓚;
-- --We say that 𝓚 is closed under the formation of homomorphic images if H(𝓚) ⊆ 𝓚,
-- --and similarly for subalgebras and products.

-- --Notice that all three of these "class operators" are designed so that for any
-- --class 𝓚, H(𝓚), S(𝓚), P(𝓚) are closed under isomorphic images.
-- --On those rare occasions that we need it, we can write I(𝓚) for the class of algebras
-- --isomorphic to a member of 𝓚.
-- --Finally, we call 𝓚 a VARIETY if it is closed under each of H, S and P.

module _ {S : Signature 𝓞 𝓥}  where

  ------------------------------------------------------------------------------
  -- Homomorphic Images.
  -- Let  ℍ  (𝓚)  denote the class of homomorphic images of members of 𝓚.

  _is-hom-image-of_ : {𝓤 : Universe} (𝑩 : Algebra (𝓤 ⁺) S) → (𝑨 : Algebra 𝓤 S)  →   𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  𝑩 is-hom-image-of 𝑨 = Σ θ ꞉ ( Rel ∣ 𝑨 ∣ _ ) , con 𝑨 θ  × ( ( ∣ 𝑨 ∣ // θ ) ≡ ∣ 𝑩 ∣ )

  HomImagesOf : (Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  HomImagesOf 𝑨 = Σ 𝑩 ꞉ (Algebra _ S) , 𝑩 is-hom-image-of 𝑨

  HomImagesOf-pred : (Algebra 𝓤 S) → Pred (Algebra ( 𝓤 ⁺ ) S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))
  HomImagesOf-pred 𝑨 = λ 𝑩 → 𝑩 is-hom-image-of 𝑨

  _is-hom-image-of-class_ : {𝓤 : Universe} → ( Algebra ( 𝓤 ⁺ ) S ) → ( Pred (Algebra 𝓤 S) (𝓤 ⁺) ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  𝑩 is-hom-image-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ S) , ( 𝑨 ∈ 𝓚 ) × ( 𝑩 is-hom-image-of 𝑨 )

  HomImagesOfClass ℍ  : {𝓤 : Universe} → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ S) , ( 𝑩 is-hom-image-of-class 𝓚 )
  ℍ 𝓚 = HomImagesOfClass 𝓚

  -- HomImagesOfClass-pred : {𝓤 : Universe} → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → Pred (Algebra ( 𝓤 ⁺ ) S ) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ )
  -- HomImagesOfClass-pred 𝓚 = λ 𝑩 → Σ 𝑨 ꞉ (Algebra _ S) ,  ( 𝑨 ∈ 𝓚 ) ×  ( 𝑩 HomImageOf 𝑨 )

  -- Here 𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ) represents a (Universe-indexed) collection of classes.
  ℍ-closed  :  (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ) )
   →           (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)  →   𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  ℍ-closed 𝓛𝓚 = λ 𝓤 𝑩 → 𝑩 is-hom-image-of-class (𝓛𝓚 𝓤) → 𝑩 ∈ (𝓛𝓚 (𝓤 ⁺) )

  ---------------------------------------------------------------------------------
  -- Products.
  -- Let ℙ (𝓚) denote the class of algebras isomorphic to a direct product of members of 𝓚.

  ℙ-closed : (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺ ) )
    →      (𝓘 : Universe )  ( I : 𝓘 ̇ )  ( 𝓐 : I → Algebra 𝓘 S )
    →      (( i : I ) → 𝓐 i ∈ 𝓛𝓚 𝓘 ) → 𝓘 ⁺ ̇
  ℙ-closed 𝓛𝓚 = λ 𝓘 I 𝓐 𝓐i∈𝓛𝓚 →  Π' 𝓐  ∈ ( 𝓛𝓚 𝓘 )

  -------------------------------------------------------------------------------------
  -- Subalgebras.
  -- Let 𝕊(𝓚) denote the class of algebras isomorphic to a subalgebra of a member of 𝓚.

  _is-subalgebra-of-class_ : {𝓤 : Universe}  (𝑩 : Algebra 𝓤 S) → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → _ ̇
  𝑩 is-subalgebra-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ S) ,  ( 𝑨 ∈ 𝓚 ) ×  (𝑩 is-subalgebra-of 𝑨)

  SubalgebraOfClass-pred_ : {𝓤 : Universe} → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) → Pred (Algebra 𝓤 S) _
  SubalgebraOfClass-pred 𝓚 = λ 𝑩 → Σ 𝑨 ꞉ (Algebra _ S) ,  ( 𝑨 ∈ 𝓚 ) ×  (𝑩 is-subalgebra-of 𝑨)

  SubalgebrasOfClass 𝕊 : {𝓤 : Universe} →  Pred (Algebra 𝓤 S) (𝓤 ⁺ )  → _ ̇
  SubalgebrasOfClass  𝓚 = Σ 𝑩 ꞉ (Algebra _ S) , (𝑩 is-subalgebra-of-class 𝓚)
  𝕊 = SubalgebrasOfClass

  SubalgebrasOfClass-pred : {𝓤 : Universe} → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) →  _ ̇
  SubalgebrasOfClass-pred 𝓚 = Σ 𝑩 ꞉ (Algebra _ S) , (SubalgebraOfClass-pred 𝓚) 𝑩

  𝕊-closed  :  (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ) )
   →      (𝓤 : Universe) → (𝑩 : Algebra 𝓤 S) → _ ̇
  𝕊-closed 𝓛𝓚 = λ 𝓤 𝑩 → (𝑩 is-subalgebra-of-class (𝓛𝓚 𝓤) ) → (𝑩 ∈ 𝓛𝓚 𝓤)

  -- 𝕊-closed-pred  :  Pred ( (𝓤 : Universe) → (Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )) ) _
  -- 𝕊-closed-pred 𝓛𝓚 = λ 𝓤 𝑩 → (SubalgebraOfClass-pred (𝓛𝓚 𝓤) ) 𝑩 → (𝑩 ∈ 𝓛𝓚 𝓤)


-- Notes on homomorphic images and their types
-- ---------------------------------------
-- The homomorphic image of f : Hom 𝑨 𝑩 is the image of ∣ 𝑨 ∣ under f, which, in "set-builder" notation, is simply Im f = {f a : a ∈ ∣ 𝑨 ∣ }.

-- As we have proved, Im f is a subuniverse of 𝑩.

-- However, there is another means of representing the collection "H 𝑨" of all homomorphic images of 𝑨 without ever referring to codomain
-- algebras (like 𝑩 above).

-- Here's how: by the first isomorphism theorem, for each f : Hom 𝑨 𝑩, there exists a congruence θ of 𝑨 (which is the kernel of f) that
-- satisfies 𝑨 / θ ≅ Im f.

-- Therefore, a nice way to get a handle on the collection H 𝑨 of all homomorphic images of 𝑨 is to simply consider the collection Con 𝑨 of
-- all congruence relations of 𝑨.  Indeed, by the above remark, we have

--   H 𝑨 = { 𝑨 / θ : θ ∈ Con 𝑨 }.

-- So, we could define the following:

--   hom-closed : (𝓚 : Pred (Algebra (𝓤 ⁺) S) l) → Pred (Algebra 𝓤 S) _
--   hom-closed 𝓚 = λ 𝑨 → (𝓚 (𝑨 / (∥𝟎∥ 𝑨)))
--     →     (∃ θ : Congruence 𝑨)  →  (∃ 𝑪 : Algebra (𝓤 ⁺) S)  →   (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)

-- To get this to type check, you can probably see the problem I was confronted with and the trick I used to resolve it.
-- The class 𝓚 is a collection of algebras whose universes live at some level.
-- (Above I used `𝓤 ⁺`.)

-- However, if 𝑨 is an algebra with ∣ 𝑨 ∣ : 𝓤 ̇, then the quotient structure  (as it is now defined in Con.agda), has type 𝑨 / θ : 𝓤 ⁺ ̇

-- So, in order for the class 𝓚 to contain both 𝑨 and all its quotients 𝑨 / θ (i.e. all its hom images) it seems we need to somehow define a class of
-- algebras that have different universe levels.

-- Can we define a data type with such "universe level polymorphism"?

-- Without that, you can see in the definition above how I got around the problem. Instead of assuming that 𝑨 itself belongs to 𝓚,
-- I assume that the "quotient" 𝑨 / ∥𝟎∥ (which is isomorphic to 𝑨) belongs to 𝓚.

-- This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if 𝑪 ≅ 𝑨 / θ ∈ 𝓚,
-- then also 𝑪 / ψ ≅ (𝑨 / θ) / ψ ∈ 𝓚.

-- So, if we want 𝓚 to be closed under all quotients, we cannot determine in advance the universe levels of the algebras that belong to 𝓚.

-- Right now I'm trying to come up with a datatype for classes of algebras that has some sort of inductive notion of the universe levels involved.

-- It seems we're testing the limits of Agda's universe level paradigm... which may be a good thing.  Maybe we can invent a cool new type to
-- solve the problem, or we may have to try to extend Agda's capabilities.

-- record AlgebraClass (ℓ : Level) : Set ℓ where
--   algebras : Pred (Algebra ℓ S) (lsuc ℓ)
--   nextclass : AlgebraClass (lsuc ℓ)

-- record AlgebraClass : Set _ where
--   algebras : (ℓ : Level) -> Pred (Algebra ℓ S) (lsuc ℓ)

--hom-closed
-- hom-closed : Pred (AlgebraClass lzero) _
-- hom-closed 𝓚 = ∀ 𝑨 -> (algebras 𝓚) 𝑨 -- (𝓚 (𝑨 / (⟦𝟎⟧ 𝑨)))
  -- -> ∀ (θ : Congruence 𝑨) -> (∃ 𝑪 : Algebra lsuc ℓ S)
  --       ------------------------------
  -- ->     (𝓚 𝑪) × ((𝑨 / θ) ≅ 𝑪)
-- Obs 2.12. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦)
-- satisfies exaxtly the same set of identities as does 𝒦.
-- module _  {i j : Level} {S : Signature i j}  where
-- open AlgebraClass

-- data HomClo {ℓ : Level} (𝓚 : AlgebraClass) : Pred AlgebraClass _ where
--   hombase : {𝑨 : Algebra ℓ S} → 𝑨 ∈ (algebras 𝓚) ℓ  → 𝑨 ∈ HomClo 𝓚
--   homstep : {𝑨 : Algebra ℓ S} ->  𝑨 ∈ HomClo 𝓚
--     ->     (∃ θ : Congruence 𝑨)
--     ->     (𝑪 : Algebra (lsuc ℓ) S)
--           ------------------------------
--     ->     𝑪 ∈ (algebras (lsuc ℓ) 𝓚) × ((𝑨 / θ) ≅ 𝑪)

-- {f : Hom 𝑨 𝑩} → 𝑨 ∈ HomClo 𝓚 → 𝑩 ∈ HClo 𝓚
--     ->   (SubunivAlg{S = S}{𝑨 = 𝑩} {HomImage{S = S}{𝑨 = 𝑨}{𝑩 = 𝑩} f} (hom-image-is-sub{S = S}{𝑨}{𝑩} f)) ∈ HClo 𝓚

-- Obs 2.13. 𝒦 ⊧ p ≈ q iff ∀ 𝑨 ∈ 𝒦, ∀ h ∈ Hom(𝑻(X_ω), 𝑨), h p^𝑨 = h q^𝑨`. (UAFST Lem 4.37)

-- Obs 2.14. Let 𝒦 be a class of algebras and p ≈ q an equation. The following are equivalent.
-- 1. 𝒦 ⊧ p ≈ q.
-- 2. (p, q) belongs to the congruence λ_𝒦 on 𝑻(X_ω).
-- 3. 𝑭_𝒦(X_ω) ⊧ p ≈ q.

-- Obs 2.15. Let 𝒦 be a class of algebras, p, q terms (say, n-ary), Y a set, and y₁,..., yₙ
-- distinct elements of Y. Then 𝒦 ⊧ p ≈ q iff p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦}(Y)(y₁, ..., yₙ).
-- In particular, 𝒦 ⊧ p ≈ q iff 𝑭_𝒦(Xₙ) ⊧ p ≈ q.

-- contains : {A : Set} -> (L : List A) -> A -> Prp
-- contains [] a = ⊥
-- contains (h :: tail) a = (h ≡ a) ⋁ (contains tail a)

----------------------------------------------------------------------------------------

-- Obs 2.5. (proved in UF-Subuniverse.agda; see sub-inter-is-sub)
-- Suppose Aᵢ ≤ 𝑨 for all i in some set I. Then ⋂ᵢ Aᵢ is a subuniverse of 𝑨. 

-- Obs 2.6. Inductive version of Sg^𝑨.  (proved in UF-Subuniverse.agda; see Sg)
-- Let 𝑨 be an algebra in the signature S and A₀ a subset of A. Define, by recursion on n, the sets Aₙ as follows:
-- If A₀ = ∅, then Aₙ = ∅ for all n<ω. If A₀ ≠ ∅, then A_{n+1} = Aₙ ∪ { f a ∣ f ∈ F, a ∈ Fin(ρ f) -> Aₙ}.
-- Then the subuniverse of 𝑨 generated by A₀ is Sg^𝑨(A₀) = ⋃ₙ Aₙ. 
-- PROOF.
--   Let Y := ⋃ₙ Aₙ. Clearly Aₙ ⊆ Y ⊆ A, for every n < ω. In particular A = A₀ ⊆ Y. We first show that  Y is a subuniverse of 𝑨.
--   Let f be a basic k-ary operation and let a: Fin(k) -> Y be a k-tuple of elements of Y. From the construction of Y,
--   ∃ n < ω, ∀ i, (a i) ∈ Aₙ. From its definition, f a ∈ A_{n+1} ⊆ Y. Since f was arbitrary, Y is a subuniverse of 𝑨 containing A₀.
--   Thus, Sg^𝑨(A₀) ⊆ Y. For the opposite inclusion, we check that Aₙ ⊆ Sg^𝑨(A₀), for each n. Clearly, A₀ ⊆ Sg^𝑨(A₀).
--   Assume Aₙ ⊆ Sg^𝑨(A₀). We must show A_{n+1} ⊆ Sg^𝑨(A₀). If b ∈ A_{n+1} - Aₙ, then b = f a for a basic k-ary operation f
--   and some a: Fin(k) -> Aₙ.  But ∀ i, a i ∈ Sg^𝑨(A₀), and this latter object is a subuniverse, so b ∈ Sg^𝑨(X) as well. Therefore,
--   A_{n+1} ⊆ Sg^𝑨(A₀), as desired.    ☐ 

-- Obs 2.7. Inductive version of Clo(F).  (UAFST Thm 4.3)
-- Let A be a set and let F ⊆ Op(A):= ⋃ₙ A^Aⁿ be a collection of operations on A. Define
--       F_0 := Proj(A) (the set of projection operations on A), and for all 0 ≤ n < ω,
--       F_{n+1} := Fₙ ∪ { f g | f ∈ F, g : Fin(ρ f) -> Fₙ ∩ (Fin(ρg) -> A) }.
-- Then Clo(F) = ⋃ₙ Fₙ.
-- PROOF.
--   Let F̄ = ⋃ₙ Fₙ. By induction, every Fₙ is a subset of Clo(F). Thus, F ⊆ Clo(F). For the converse inclusion, we must show F` is
--   a clone that contains F. Obviously F contains the projection operations, F₀ ⊆ F̄. For every f ∈ F, we have f πᵏ ∈ F₁ ⊆ F̄,
--   where k := ρ f. We must show that F̄ is closed under generalized composition. This follows from the following subclaim.
--   SUBCLAIM. If f ∈ Fₙ and all entries of g := (g₀, ..., g_{ρf - 1} ∈ Fₘ are k-ary, then f g ∈ F_{n+m},
--             where we have defined g: Fin(ρ f) -> (k -> A) -> A to be the tuple given by g i = gᵢ for
--             each 0 ≤ i < ρ f.
--
--   By induction on n: If n = 0 then f is a projection, so f g = gᵢ ∈ Fₘ for some 0 ≤ i < ρ f. Assume (IH) claim holds for n and
--   f ∈ F_{n+1} - Fₙ.  By def, ∃ t-ary op fᵢ ∈ F, ∃ t-tuple, h = (h₀, ..., h_{t-1}) ∈ t -> Fₙ, such that f = fᵢ h.
--   (N.B. h: Fin(t)  →  (Fin(ρ f)  →   A)   →   A is given by h(j) = hⱼ, and the arity of each hᵢ must be equal to that of f, namely ρ f.)
--   By (IH) for each i ≤ k, hᵢ = hᵢ g ∈ F_{n+m}, where as above g = (g₀,...,g_{k-1}). By def, f₁ h' ∈ F_{n+m+1} = F_{(n+1)+m}.
--   Since f₁ h' = f₁ ∘ (h₁ g, ..., hₜ g) = f g, the claim is proved. □

-- Obs 2.8. Lift of a map h : X → A extends uniquly to a hom 𝑻(X) → 𝑨.  (UAFST Thm 4.21)
-- 1. 𝑻 := 𝑻_σ(X) is generated by X.
-- 2. ∀ 𝑨 = ⟨A, F^𝑨⟩, ∀ g: X → A, ∃! hom h: 𝑻 → 𝑨,  h|_X = g.
-- (proved in Free.agda; see `free-unique`)
-- PROOF.
--   The def of 𝑻 exactly parallels the construction in Obs 6 above. That accounts for the 1st assertion. For the 2nd assertion,
--   define h t by induction on the height, |t|, of t. Suppose |t| = 0.  Then t ∈ X ∪ F₀. If t ∈ X, then define h t = g t. If t ∈ F₀,
--   then let h t = t^𝑨. For the inductive step, assume |t| = n+1. Then t = f s for some f ∈ F and s: Fin(ρ f) -> Tₙ, where for
--   each 0 ≤ i< ρ f the term s i has height at most n. Define h t = f^𝑨(h ∘ s) = f^𝑨(h s₁, ..., h sₖ). Then h is a hom that agrees with
--   g on X. The uniqueness of h follows from Obs 2. ☐

-- Obs 2.9. Homs commute with terms. (UAFST Thm 4.32)
-- (proved in UF-Free.agda; see `comm-hom-term`)

-- Obs 2.10. Terms respect congruences.
-- (proved in UF-Free.agda; see `compatible-term`)

-- Obs 2.11. On subuniverse generation as image of terms. (Proved in UF-Subuniverse.agda; see TermImageIsSub)
-- If Y is a subset of A, then Sg^{𝑨}(Y) = { t^𝑨 a : t ∈ T_σ(X_n), n ∈ ℕ, a: Fin(ρ t) -> Y }.
-- PROOF.
--   Induction on the height of t shows that every subuniverse is closed under the action of t^𝑨. Thus the right-hand side is contained
--   in the left. On the other hand, the right-hand side is a subuniverse that contains the elements of Y (take t = x₁), so it contains
--   Sg^{𝑨}(Y), as the latter is the smallest subuniverse containing Y. ☐

-- Obs 2.12. ∀ 𝒦 (classes of structures) each of the classes 𝖲(𝒦), 𝖧(𝒦), 𝖯(𝒦), 𝕍(𝒦) satisfies the same set of identities as does 𝒦.
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
--   We shall show (1) ⟹ (3) ⟹ (2) ⟹ (1).  Recall that 𝑭_𝒦(X_ω) = 𝑻/λ ∈ 𝖲 𝖯 (𝒦).  From (1) and Lemma 4.36 of :term:`UAFST`
--   we have 𝖲 𝖯 (𝒦) ⊧ p ≈ q. Thus (3) holds. From (3), p^𝑭 [x] = q^𝑭 [x], where [x]: Fin(ρ p) → 𝑭_𝒦 (X_ω) is defined by [x] i = xᵢ/λ.
--   From the def of 𝑭, p^𝑻 x ≡λ q^𝑻 x, from which (2) follows since p = p^𝑻 x and q = q^𝑻 x.  Finally assume (2). We wish to
--   apply Lemma 4.37 of UAFST. Let 𝑨 ∈ 𝒦 and h ∈ Hom(𝑻, 𝑨). Then 𝑻/ker h ∈ 𝖲 (𝑨) ⊆ 𝖲(𝒦) so ker h ⊇ λ.  Thus, (2) implies
--   h p = h q hence (1) holds. ☐

-- The last result tells us that we can determine whether an identity is true in a variety by consulting a particular algebra, namely
-- 𝑭(X_ω). Sometimes it is convenient to work with algebras free on other generating sets besides X_ω. The following corollary
-- takes care of that for us.

-- Obs 2.15. Let 𝒦 be a class of algebras, p, q terms (say, n-ary), Y a set, and y₁,..., yₙ distinct elements of Y.
-- Then 𝒦 ⊧ p ≈ q iff p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦}(Y)(y₁, ..., yₙ). In particular, 𝒦 ⊧ p ≈ q iff 𝑭_𝒦(Xₙ) ⊧ p ≈ q.
-- PROOF. Since 𝑭_𝒦(Y) ∈ 𝖲 𝖯 (𝒦), the left-to-right direction uses the same argument as in Thm 4.38 of UAFST. (See Obs 14 above.)
--   So assume that p^{𝑭_𝒦(Y)}(y₁,..., yₙ) = q^{𝑭_𝒦(Y)}(y₁,..., yₙ). To show that 𝒦 ⊧ p ≈ q, let 𝑨= ⟨ A, f^𝑨 ⟩ ∈ 𝒦 and a₁, ..., aₙ ∈ A.
--   We must show p^𝑨(a₁,..., aₙ) = q^𝑨(a₁,...,aₙ)`. There is a hom h: 𝔽_𝒦(Y) -> (A, f^𝑨) such that h(yᵢ) = aᵢ for i ≤ n. Then
--   p^𝑨(a₁, ..., aₙ) = p^𝑨(h(y₁), ..., h(yₙ)) = h(p^{𝑭_𝒦(Y)}(y₁, ...,yₙ)) = h(q^{𝑭_𝒦(Y)}(y₁, ...,yₙ)) = q^𝑨(h(y₁), ..., h(yₙ)) = q^𝑨(a₁, ..., aₙ).
--   It now follows from Obs 12 that every equational class is a variety.  ☐
--
--        (The converse of Obs 2.15 is **Birkhoff's HSP Theorem**.)
--
-- Obs 2.16. Every  finitely  generated  variety  is  locally finite. (UAFST Thm 3.49)
-- (This is not needed for the HSP theorem, but we might want to prove it next.)
--
-- The converse of the last theorem is false.  That is, ∃ loc fin varieties that are not finitely generated
-- (e.g., the variety of p-algebras; see UAFSt Cor. 4.55).


