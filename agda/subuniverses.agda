-- FILE: subuniverses.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020

{-# OPTIONS --without-K --exact-split --safe #-}

open import prelude
open import basic using (Signature; Algebra; Op; _̂_)
open import relations using (transitive)
open import homomorphisms using (HOM; Hom; hom; is-homomorphism; HomImage)

open import terms using (Term; _̇_; generator; node;
 comm-hom-term; comm-hom-term')

open import Relation.Unary using (⋂)

module subuniverses {S : Signature 𝓞 𝓥} where

Subuniverses : (A : Algebra 𝓤 S)
 →             Pred (Pred ∣ A ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)

Subuniverses (A , FA) B =
 (f : ∣ S ∣)(a : ∥ S ∥ f → A) → Im a ⊆ B → FA f a ∈ B

data _is-supalgebra-of_
 (A : Algebra 𝓤 S) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) where
  mem : (B : Pred ∣ A ∣ 𝓤) (F : (f : ∣ S ∣)
   →    Op (∥ S ∥ f) (Σ B)) → ((f : ∣ S ∣)(a : ∥ S ∥ f → Σ B)
   →    ∣ F f a ∣ ≡ ∥ A ∥ f (λ i → ∣ a i ∣))
   →    A is-supalgebra-of (Σ B , F)

_is-subalgebra-of_ : Algebra 𝓤 S → Algebra 𝓤 S → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
B is-subalgebra-of A = A is-supalgebra-of B

_is-subalgebra-of-class_ : {𝓤 : Universe}(B : Algebra 𝓤 S)
 →            Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
B is-subalgebra-of-class 𝒦 =
   Σ A ꞉ (Algebra _ S) , (A ∈ 𝒦) × (B is-subalgebra-of A)

module _
 {A : Algebra 𝓤 S} {B : Pred ∣ A ∣ 𝓤}
 {F : (f : ∣ S ∣) → Op (∥ S ∥ f) (Σ B)}
 (B∈SubA : B ∈ Subuniverses A) where

 SubunivAlg : Algebra 𝓤 S
 SubunivAlg =
  Σ B , λ f x → ∥ A ∥ f (∣_∣ ∘ x) , B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

 subuniv-to-subalg : SubunivAlg is-subalgebra-of A
 subuniv-to-subalg = mem B ∥ SubunivAlg ∥ λ f a → (refl _)

record Subuniverse {A : Algebra 𝓤 S} : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇ where
 constructor mksub
 field
   sset  : Pred ∣ A ∣ 𝓤
   isSub : sset ∈ Subuniverses A

module _ {A : Algebra 𝓤 S} where

 data Sg (X : Pred ∣ A ∣ 𝓣) : Pred ∣ A ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣) where
  var : ∀ {v} → v ∈ X → v ∈ Sg X
  app :  ( f : ∣ S ∣ ) { a : ∥ S ∥ f → ∣ A ∣ }
   →       Im a ⊆ Sg X
          -----------------
   →       ∥ A ∥ f a ∈ Sg X

 sgIsSub : (X : Pred ∣ A ∣ 𝓤) → Sg X ∈ Subuniverses A
 sgIsSub _ f a α = app f α

 sgIsSmallest : {X : Pred ∣ A ∣ 𝓡} {Y : Pred ∣ A ∣ 𝓢}
  →             Y ∈ Subuniverses A
  →             X ⊆ Y
               -----------------
  →              Sg X ⊆ Y

 -- By induction on x ∈ Sg X, show x ∈ Y
 sgIsSmallest _ X⊆Y (var v∈X) = X⊆Y v∈X

 sgIsSmallest {Y = Y} YIsSub X⊆Y (app f {a} ima⊆SgX) = app∈Y
  where
   -- First, show the args are in Y
   ima⊆Y : Im a ⊆ Y
   ima⊆Y i = sgIsSmallest YIsSub X⊆Y (ima⊆SgX i)

   --Since Y is a subuniverse of A, it contains the application
   app∈Y : ∥ A ∥ f a ∈ Y          --           of f to said args.
   app∈Y = YIsSub f a ima⊆Y

module _
 {A : Algebra 𝓤 S} {I : 𝓘 ̇}
 {𝒜 : I → Pred ∣ A ∣ 𝓣} where

 sub-inter-is-sub : ((i : I) → 𝒜 i ∈ Subuniverses A)
  →                 ⋂ I 𝒜 ∈ Subuniverses A

 sub-inter-is-sub Ai-is-Sub f a ima⊆⋂A = α
  where
   α : ∥ A ∥ f a ∈ ⋂ I 𝒜
   α i = Ai-is-Sub i f a λ j → ima⊆⋂A j i


module _
 {X : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ̇}
 {A B : Algebra 𝓤 S}
 {B : Pred ∣ A ∣ 𝓤}
 (Y : 𝓤 ̇) where

 sub-term-closed : B ∈ Subuniverses A
  →                (t : Term)(b : X → ∣ A ∣)
  →                (∀ i → b i ∈ B)
                 ---------------------------
  →                ((t ̇ A) b) ∈ B

 sub-term-closed B≤A (generator x) b b∈B = b∈B x

 sub-term-closed B≤A (node f t) b b∈B =
   B≤A f (λ z → (t z ̇ A) b)
         (λ x → sub-term-closed B≤A (t x) b b∈B)

 data TermImage (Y : Pred ∣ A ∣ 𝓤) : Pred ∣ A ∣ (𝓞 ⊔ 𝓥 ⊔ 𝓤) where
  var : ∀ {y : ∣ A ∣} → y ∈ Y → y ∈ TermImage Y
  app : (f : ∣ S ∣) (t : ∥ S ∥ f → ∣ A ∣)
   →    (∀ i  →  t i ∈ TermImage Y)
       -------------------------------
   →    (∥ A ∥ f t) ∈ TermImage Y

 --1. TermImage is a subuniverse
 TermImageIsSub : (Y : Pred ∣ A ∣ 𝓤)
  →               TermImage Y ∈ Subuniverses A

 TermImageIsSub Y = λ f a x → app f a x

 --2. Y ⊆ TermImageY
 Y⊆TermImageY : (Y : Pred ∣ A ∣ 𝓤)
  →             Y ⊆ TermImage Y

 Y⊆TermImageY Y {a} a∈Y = var a∈Y

 -- 3. Sg^A(Y) is the smallest subuniverse containing Y
 --    Proof: see `sgIsSmallest`

 SgY⊆TermImageY : (Y : Pred ∣ A ∣ 𝓤) → Sg Y ⊆ TermImage Y
 SgY⊆TermImageY Y = sgIsSmallest (TermImageIsSub Y)
                                 (Y⊆TermImageY Y)



module _ {A : Algebra 𝓤 S} (UV : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext UV

 op-closed : (∣ A ∣ → 𝓦 ̇) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 op-closed B = (f : ∣ S ∣)(a : ∥ S ∥ f → ∣ A ∣)
  → ((i : ∥ S ∥ f) → B (a i)) → B (∥ A ∥ f a)

 subuniverse : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 subuniverse = Σ B ꞉ (𝓟 ∣ A ∣) , op-closed ( _∈₀ B)

 being-op-closed-is-subsingleton : (B : 𝓟 ∣ A ∣)
  →           is-subsingleton (op-closed ( _∈₀ B ))
 being-op-closed-is-subsingleton B = Π-is-subsingleton gfe
  (λ f → Π-is-subsingleton gfe
   (λ a → Π-is-subsingleton gfe
    (λ _ → ∈-is-subsingleton B (∥ A ∥ f a))))

 pr₁-is-embedding : is-embedding ∣_∣
 pr₁-is-embedding = pr₁-embedding being-op-closed-is-subsingleton

 --so equality of subalgebras is equality of their underlying
 --subsets in the powerset:
 ap-pr₁ : (B C : subuniverse) → B ≡ C → ∣ B ∣ ≡ ∣ C ∣
 ap-pr₁ B C = ap ∣_∣

 ap-pr₁-is-equiv : (B C : subuniverse) → is-equiv (ap-pr₁ B C)
 ap-pr₁-is-equiv =
  embedding-gives-ap-is-equiv ∣_∣ pr₁-is-embedding

 subuniverse-is-a-set : is-set subuniverse
 subuniverse-is-a-set B C = equiv-to-subsingleton
                           (ap-pr₁ B C , ap-pr₁-is-equiv B C)
                           (powersets-are-sets' UV ∣ B ∣ ∣ C ∣)

 subuniverse-equality-gives-membership-equiv : (B C : subuniverse)
  →                                  B ≡ C
                      -----------------------------------
  →                   ( x : ∣ A ∣ ) → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣)
 subuniverse-equality-gives-membership-equiv B C B≡C x =
  transport (λ - → x ∈₀ ∣ - ∣) B≡C ,
   transport (λ - → x ∈₀ ∣ - ∣ ) ( B≡C ⁻¹ )

 membership-equiv-gives-carrier-equality : (B C : subuniverse)
  →          ((x : ∣ A ∣) →  x ∈₀ ∣ B ∣  ⇔  x ∈₀ ∣ C ∣)
            -----------------------------------------
  →                       ∣ B ∣ ≡ ∣ C ∣
 membership-equiv-gives-carrier-equality B C φ =
  subset-extensionality' UV α β
   where
    α :  ∣ B ∣ ⊆₀ ∣ C ∣
    α x = lr-implication (φ x)

    β : ∣ C ∣ ⊆₀ ∣ B ∣
    β x = rl-implication (φ x)

 membership-equiv-gives-subuniverse-equality : (B C : subuniverse)
  →            (( x : ∣ A ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
               ---------------------------------------
  →                          B ≡ C
 membership-equiv-gives-subuniverse-equality B C =
  inverse (ap-pr₁ B C)
  (ap-pr₁-is-equiv B C)
     ∘ (membership-equiv-gives-carrier-equality B C)

 membership-equiv-is-subsingleton : (B C : subuniverse)
  →    is-subsingleton (( x : ∣ A ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣)
 membership-equiv-is-subsingleton B C =
  Π-is-subsingleton gfe
   (λ x → ×-is-subsingleton
    (Π-is-subsingleton gfe (λ _ → ∈-is-subsingleton ∣ C ∣ x ))
      (Π-is-subsingleton gfe (λ _ → ∈-is-subsingleton ∣ B ∣ x )))

 subuniverse-equality : (B C : subuniverse)
  →    (B ≡ C)  ≃  ((x : ∣ A ∣)  → (x ∈₀ ∣ B ∣) ⇔ (x ∈₀ ∣ C ∣))

 subuniverse-equality B C =
  logically-equivalent-subsingletons-are-equivalent _ _
    (subuniverse-is-a-set B C)
     (membership-equiv-is-subsingleton B C)
      (subuniverse-equality-gives-membership-equiv B C ,
        membership-equiv-gives-subuniverse-equality B C)

 carrier-equality-gives-membership-equiv : (B C : subuniverse)
  →                            ∣ B ∣ ≡ ∣ C ∣
                ----------------------------------------
  →              ( ( x : ∣ A ∣ ) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣ )
 carrier-equality-gives-membership-equiv B C (refl _) x = id , id

 --so we have...
 carrier-equiv : (B C : subuniverse)
  →   ((x : ∣ A ∣) → x ∈₀ ∣ B ∣ ⇔ x ∈₀ ∣ C ∣) ≃ (∣ B ∣ ≡ ∣ C ∣)
 carrier-equiv B C =
  logically-equivalent-subsingletons-are-equivalent _ _
   (membership-equiv-is-subsingleton B C)
    (powersets-are-sets' UV ∣ B ∣ ∣ C ∣)
     (membership-equiv-gives-carrier-equality B C ,
       carrier-equality-gives-membership-equiv B C)

 -- ...which yields an alternative subuniverse equality lemma.
 subuniverse-equality' : (B C : subuniverse)
  →                      (B ≡ C) ≃ (∣ B ∣ ≡ ∣ C ∣)
 subuniverse-equality' B C =
  (subuniverse-equality B C) ● (carrier-equiv B C)


 -- new definition of subalgebra (includes an embedding)
 Subalgebra : 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 Subalgebra = Σ B ꞉ (Algebra 𝓤 S) ,
                 Σ h ꞉ (∣ B ∣ → ∣ A ∣) ,
                   is-embedding h × is-homomorphism B A h

module _
 {𝓤 : Universe}
 {X : 𝓧 ̇ }
 {UV : Univalence} where

 _⊧_≈_ : {X : 𝓧 ̇ } → Algebra 𝓤 S
  →      Term{X = X} → Term → 𝓧 ⊔ 𝓤 ̇

 A ⊧ p ≈ q = (p ̇ A) ≡ (q ̇ A)

 _⊧_≋_ : Pred (Algebra 𝓤 S) 𝓦
  →      Term{X = X} → Term → 𝓞 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧 ⊔ 𝓤 ⁺ ̇

 _⊧_≋_ 𝒦 p q = {A : Algebra _ S} → 𝒦 A → A ⊧ p ≈ q

 gdfe : global-dfunext
 gdfe = univalence-gives-global-dfunext UV

 SubalgebrasOfClass : Pred (Algebra 𝓤 S)(𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 SubalgebrasOfClass 𝒦 =
  Σ A ꞉ (Algebra _ S) , (A ∈ 𝒦) × Subalgebra{A = A} UV

 data SClo (𝒦 : Pred (Algebra 𝓤 S) (𝓤 ⁺)) : Pred (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ) where
  sbase : {A :  Algebra _ S} → A ∈ 𝒦 → A ∈ SClo 𝒦
  sub : (SAK : SubalgebrasOfClass 𝒦) → (pr₁ ∥ (pr₂ SAK) ∥) ∈ SClo 𝒦

 S-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
  →      (𝓤 : Universe) → (B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
 S-closed ℒ𝒦 =
  λ 𝓤 B → (B is-subalgebra-of-class (ℒ𝒦 𝓤)) → (B ∈ ℒ𝒦 𝓤)

 subalgebras-preserve-identities : (𝒦 : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ ))(p q : Term{X = X})
  →  (𝒦 ⊧ p ≋ q) → (SAK : SubalgebrasOfClass 𝒦)
  →  (pr₁ ∥ (pr₂ SAK) ∥) ⊧ p ≈ q
 subalgebras-preserve-identities 𝒦 p q 𝒦⊧p≋q SAK = γ
  where

  A : Algebra 𝓤 S
  A = ∣ SAK ∣

  A∈𝒦 : A ∈ 𝒦
  A∈𝒦 = ∣ pr₂ SAK ∣

  A⊧p≈q : A ⊧ p ≈ q
  A⊧p≈q = 𝒦⊧p≋q A∈𝒦

  subalg : Subalgebra{A = A} UV
  subalg = ∥ pr₂ SAK ∥

  B : Algebra 𝓤 S
  B = pr₁ subalg

  h : ∣ B ∣ → ∣ A ∣
  h = ∣ pr₂ subalg ∣

  hem : is-embedding h
  hem = pr₁ ∥ pr₂ subalg ∥

  hhm : is-homomorphism B A h
  hhm = pr₂ ∥ pr₂ subalg ∥

  ξ : (b : X → ∣ B ∣ ) → h ((p ̇ B) b) ≡ h ((q ̇ B) b)
  ξ b =
   h ((p ̇ B) b)  ≡⟨ comm-hom-term' gdfe B A (h , hhm) p b ⟩
   (p ̇ A)(h ∘ b) ≡⟨ intensionality A⊧p≈q (h ∘ b) ⟩
   (q ̇ A)(h ∘ b) ≡⟨ (comm-hom-term' gdfe B A (h , hhm) q b)⁻¹ ⟩
   h ((q ̇ B) b)  ∎

  hlc : {b b' : domain h} → h b ≡ h b' → b ≡ b'
  hlc hb≡hb' = (embeddings-are-lc h hem) hb≡hb'

  γ : B ⊧ p ≈ q
  γ = gdfe λ b → hlc (ξ b)


-- Hom image is subuniverse
module _ {A B : Algebra 𝓤 S} (h : hom A B)  where
 hom-image-is-sub : {funext 𝓥 𝓤} → (HomImage{A = A}{B = B} h) ∈ Subuniverses B
 hom-image-is-sub {fe} f b b∈Imf =
  eq (∥ B ∥ f b) ( ∥ A ∥ f ar) γ
   where
    ar : ∥ S ∥ f → ∣ A ∣
    ar = λ x → Inv ∣ h ∣ (b x) (b∈Imf x)

    ζ : ∣ h ∣ ∘ ar ≡ b
    ζ = fe (λ x → InvIsInv ∣ h ∣ (b x) (b∈Imf x))

    γ : ∥ B ∥ f b
         ≡ ∣ h ∣ (∥ A ∥ f (λ x → Inv ∣ h ∣ (b x)(b∈Imf x)))
    γ = ∥ B ∥ f b            ≡⟨ ap ( ∥ B ∥ f ) (ζ ⁻¹) ⟩
        (∥ B ∥ f)(∣ h ∣ ∘ ar) ≡⟨ ( ∥ h ∥ f ar ) ⁻¹ ⟩
        ∣ h ∣ (∥ A ∥ f ar)    ∎

-- HOM image is subuniverse
module intensional-hom-image
 {A B : Algebra 𝓤 S} (h : HOM A B)  where

 open homomorphisms.intensional-hom-image
 HOM-image-is-sub : funext 𝓥 𝓤 → (HOMImage{A = A}{B = B} h) ∈ Subuniverses B
 HOM-image-is-sub fe f b b∈Imh = eq (∥ B ∥ f b) (∥ A ∥ f ar) γ
  where
   ar : ∥ S ∥ f → ∣ A ∣
   ar = λ x → Inv ∣ h ∣ (b x) (b∈Imh x)

   ζ : (λ x → ∣ h ∣ (ar x)) ≡ (λ x → b x)
   ζ = fe (λ x → InvIsInv ∣ h ∣ (b x) (b∈Imh x) )

   γ : ∥ B ∥ f (λ x → b x)
        ≡ ∣ h ∣ (∥ A ∥ f (λ x → Inv ∣ h ∣ (b x) (b∈Imh x)))
   γ = ∥ B ∥ f (λ x → b x)   ≡⟨ ap (∥ B ∥ f) ζ ⁻¹ ⟩
       (∥ B ∥ f) (∣ h ∣ ∘ ar)  ≡⟨ intensionality ξ ar ⟩
       ∣ h ∣ (∥ A ∥ f ar)      ∎
    where
     τ : (λ f ar → (∥ B ∥ f)(∣ h ∣ ∘ ar))
          ≡ (λ f ar → ∣ h ∣ (∥ A ∥ f ar ))
     τ = ∥ h ∥ ⁻¹
     ξ : (λ (ar : ∥ S ∥ f → ∣ A ∣) → (∥ B ∥ f)(∣ h ∣ ∘ ar))
          ≡ (λ (ar : ∥ S ∥ f → ∣ A ∣) → ∣ h ∣ (∥ A ∥ f ar))
     ξ = dep-intensionality τ f

 hinv' : {X : 𝓤 ̇ } (b : X → ∣ (HOM-image-alg{A = A}{B = B} h) ∣) (x : X) → ∣ A ∣
 hinv' = λ b x → Inv ∣ h ∣ ∣ b x ∣ ∥ b x ∥



-- --------------------------------------------------------------------------------------------------

-- Notes on homomorphic images and their types
-- --------------------------------------------

-- The homomorphic image of `f : Hom A B` is the image of `∣ A ∣` under `f`, which, in "set-builder" notation, is simply `Im f = {f a : a ∈ ∣ A ∣ }`.

-- As we have proved, `Im f` is a subuniverse of `B`.

-- However, there is another means of representing the collection "H A" of all homomorphic images of A without ever referring to codomain algebras (like B above).

-- Here's how: by the first isomorphism theorem, for each `f : Hom A B`, there exists a congruence `θ` of `A` (which is the kernel of `f`) that satisfies `A / θ ≅ Im f`.

-- Therefore, we have a handle on the collection `H A` of all homomorphic images of `A` if we simply consider the collection `Con A` of all congruence relations of `A`.  Indeed, by the above remark, we have

--   `H A = { A / θ : θ ∈ Con A }`.

-- So, we could define the following:

-- .. code-block::

--    hom-closed : (𝒦 : Pred (Algebra (𝓤 ⁺) S) l)
--     →           Pred (Algebra 𝓤 S) _
--     hom-closed 𝒦 = λ A → (𝒦 (A / (∥𝟎∥ A)))
--       →             (∃ θ : Congruence A)
--       →             (∃ C : Algebra (𝓤 ⁺) S)
--       →             (𝒦 C) × ((A / θ) ≅ C)

-- To get this to type check, we have an apparent problem, and we need a trick to resolve it. The class 𝒦 is a collection of algebras whose universes live at some level. (Above we use `𝓤 ⁺`.)

-- However, if `A` is an algebra with `∣ A ∣ : 𝓤 ̇`, then the quotient structure  (as it is now defined in Con.agda), has type `A / θ : 𝓤 ⁺ ̇`. So, in order for the class `𝒦` to contain both `A` and all its quotients `A / θ` (i.e. all its homomorphic images), we need to somehow define a class of algebras that have different universe levels.

-- Can we define a data type with such "universe level polymorphism"?

-- Without that, we use a trick to get around the problem. Instead of assuming that `A` itself belongs to `𝒦`, we could instead take the "quotient" `A / ∥𝟎∥` (which is isomorphic to `A`) as belonging to `𝒦`.

-- This is a hack and, worse, it won't do for us. We need something inductive because we will also need that if `C ≅ A / θ ∈ 𝒦`, then also `C / ψ ≅ (A / θ) / ψ ∈ 𝒦`.

-- So, if we want `𝒦` to be closed under all quotients, we cannot determine in advance the universe levels of the algebras that belong to `𝒦`.

-- We are trying to come up with a datatype for classes of algebras that has some sort of inductive notion of the universe levels involved.

-- It seems we may be testing the limits of Agda's universe level paradigm. Maybe we can invent a new type to solve the problem, or we may have to try to extend Agda's capabilities.

-- ..
--    record AlgebraClass (𝓤 : Universe) : 𝓤 ̇ where
--     algebras : Pred (Algebra 𝓤 S) ( 𝓤 ⁺ )
--     nextclass : AlgebraClass ( 𝓤 ⁺ )

--    record AlgebraClass : Set _ where
--     algebras : (ℓ : Level) -> Pred (Algebra ℓ S) (lsuc ℓ)

--    module _ {S : Signature 𝓞 𝓥} where

--     hom-closed : Pred (AlgebraClass lzero) _
--     hom-closed 𝒦 = ∀ A -> (algebras 𝒦) A -- (𝒦 (A / (⟦𝟎⟧ A)))
--      -> ∀ (θ : Congruence A) -> (∃ C : Algebra lsuc ℓ S)
--           ------------------------------
--      ->     (𝒦 C) × ((A / θ) ≅ C)


--    module _  {S : Signature 𝓞 𝓥}  where
--     open AlgebraClass

--     data HomClo {ℓ : Level} (𝒦 : AlgebraClass) : Pred AlgebraClass _ where
--      hombase : {A : Algebra ℓ S} → A ∈ (algebras 𝒦) ℓ  → A ∈ HomClo 𝒦
--      homstep : {A : Algebra ℓ S} ->  A ∈ HomClo 𝒦
--        ->     (∃ θ : Congruence A)
--        ->     (C : Algebra (lsuc ℓ) S)
--              ------------------------------
--        ->     C ∈ (algebras (lsuc ℓ) 𝒦) × ((A / θ) ≅ C)


