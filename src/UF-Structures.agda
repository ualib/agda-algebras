--FILE: UF-Structures.agda
--BLAME: williamdemeo@gmail.com
--DATE: 22 Apr 2020
--UPDATE: 29 May 2020
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sip 
--      In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--      Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Structures where

open import UF-Prelude using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇; _⊔_; universe-of; id; 𝑖𝑑; _∘_; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; _×_; _≡_; refl; _∼_; transport; _≡⟨_⟩_; _∎; ap; _∙_; _⁻¹; _⇔_; _iff_; lr-implication; rl-implication; ∣_∣; ∥_∥)

open import UF-Singleton using (is-set; is-subsingleton; singletons-are-subsingletons)

open import UF-Equality using (refl-left ; ap-id; singleton-type'; singleton-types'-are-singletons; _≃_;  id-≃; is-equiv; id-is-equiv; Σ-≡-≃; Σ-cong; ≃-sym; _≃⟨_⟩_; _■; ∘-is-equiv; inverse; to-×-≡; ap-pr₁-to-×-≡; ap-pr₂-to-×-≡; inverses-are-sections; fiber; fiber-point; fiber-identification; Σ-flip)

open import UF-Extensionality using (∃!; -∃!; being-set-is-subsingleton; univalence-gives-dfunext; dfunext; Π-is-subsingleton; hfunext; univalence-gives-hfunext; Π-is-set; Univalence; global-dfunext; univalence-gives-global-dfunext; 𝓟; _∈_; ∈-is-subsingleton; powersets-are-sets'; _⊆_; subset-extensionality'; ⊆-is-subsingleton)

open import UF-Univalence using (is-univalent; Id→Eq; Σ-assoc; equivs-closed-under-∼; ap₂; ×-is-subsingleton; to-subtype-≡; equiv-to-subsingleton; logically-equivalent-subsingletons-are-equivalent; left-cancellable; subtypes-of-sets-are-sets; Σ-change-of-variable)

open import UF-Embedding using (is-embedding; pr₁-embedding; embedding-gives-ap-is-equiv; fiberwise-retractions-are-equivs; universal-fiberwise-equiv; embeddings-are-lc; _↪_; Subtypes; χ-special; χ-special-is-equiv)

open import UF-Algebra using (SNS; ⟨_⟩; canonical-map; characterization-of-≡; _≃[_]_)

-------------------------------------------------------------------------------------------------
--∞-Magmas.
module ∞-magma-identity {𝓤 : Universe} where
  ∞-magma-structure : 𝓤 ̇ → 𝓤 ̇
  ∞-magma-structure X = X → X → X

  ∞-Magma : 𝓤 ⁺ ̇
  ∞-Magma = Σ X ꞉ 𝓤 ̇ , ∞-magma-structure X

  --Standard notion of structure (SNS) for ∞-Magmas
  sns-data : SNS ∞-magma-structure 𝓤
  sns-data = (ι , ρ , θ)
   where
    ι : (A 𝑩 : ∞-Magma) →  ⟨ A ⟩ ≃ ⟨ 𝑩 ⟩  → 𝓤 ̇
    ι (X , _·_) (Y , _*_) (f , _) = (λ x x' → f (x · x')) ≡ (λ x x' → f x * f x')

    ρ : (A : ∞-Magma) → ι A A (id-≃ ⟨ A ⟩)
    ρ (X , _·_) = refl _·_

    h : {X : 𝓤 ̇ } {_·_ _*_ : ∞-magma-structure X}
      → canonical-map ι ρ _·_ _*_ ∼ 𝑖𝑑 (_·_ ≡ _*_)

    h (refl _·_) = refl (refl _·_)

    θ : {X : 𝓤 ̇ } (_·_ _*_ : ∞-magma-structure X) → is-equiv (canonical-map ι ρ _·_ _*_)

    θ _·_ _*_ = equivs-closed-under-∼ ( id-is-equiv (_·_ ≡ _*_) ) h

  _≅_ : ∞-Magma → ∞-Magma → 𝓤 ̇

  (X , _·_) ≅ (Y , _*_) =

            Σ f ꞉ (X → Y), is-equiv f
                         × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))

  characterization-of-∞-Magma-≡ : is-univalent 𝓤 → (A 𝑩 : ∞-Magma) → (A ≡ 𝑩) ≃ (A ≅ 𝑩)
  characterization-of-∞-Magma-≡ 𝓤★ = characterization-of-≡ 𝓤★ sns-data

  --"The above equivalence is characterized by induction on identifications as the function that maps reflexivity to the identity equivalence:
  characterization-of-characterization-of-∞-Magma-≡ : (𝓤★ : is-univalent 𝓤) (A : ∞-Magma)
   →       ∣ characterization-of-∞-Magma-≡ 𝓤★ A A ∣ (refl A)    ≡    ( 𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _ )
  characterization-of-characterization-of-∞-Magma-≡ 𝓤★ A = refl _

--ADDING AXIOMS.
--"We account for axioms using a submodule and by reduction to the characterization of identifications given in the module `UF-Algebra`."
module uf-algebra-with-axioms where
  --(paraphrasing MHE) Given structure map `S` and subsingleton-valued axioms for types with structure `S`, the first construction
  --builds `SNS` data on `S'` defined by `S' X = Σ s ꞉ S X , axioms X s` from given `SNS` data on `S`.

  --For this MHE first defines a forgetful map `Σ S' → Σ S` and an underlying-type function `Σ S → 𝓤`:
  [_] : {S : 𝓤 ̇ → 𝓥 ̇} {axioms : (X : 𝓤 ̇) → S X → 𝓦 ̇}
   →  (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → Σ S
  [ X , s , _ ] = (X , s)

  ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇} {axioms : (X : 𝓤 ̇) → S X → 𝓦 ̇}
   →  (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → 𝓤 ̇
  ⟪ X , _ , _ ⟫ = X           -- NOTATION. Type ⟪ and ⟫ as `\<<` and `\>>`.

  --"In the following construction:
  --    * For `ι'` and `ρ'` we use `ι` and `ρ` ignoring the axioms.
  --    * For `θ'` we need more work, but the essence of the construction is the fact that the projection`S' X → S X`
  --      that forgets the axioms is an embedding precisely because the axioms are subsingleton-valued.
  add-axioms : {S : 𝓤 ̇ → 𝓥 ̇}  (axioms : (X : 𝓤 ̇) → S X → 𝓦 ̇)
   →             ( (X : 𝓤 ̇)  (s : S X)  →  is-subsingleton (axioms X s) )
   →             SNS S 𝓣
   →             SNS (λ X → Σ s ꞉ S X , axioms X s) 𝓣

  add-axioms {𝓤}{𝓥}{𝓦}{𝓣}{S} axioms axiomsXs✧ (ι , ρ , θ) = ι' , ρ' , θ'
   where
    S' : 𝓤 ̇ → 𝓥 ⊔ 𝓦 ̇
    S' X = Σ s ꞉ S X , axioms X s

    ι' : ( A 𝑩 : Σ S' ) → ⟨ A ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓣 ̇
    ι' A 𝑩 = ι [ A ] [ 𝑩 ]

    ρ' : (A : Σ S') → ι' A A (id-≃ ⟨ A ⟩)
    ρ' A = ρ [ A ]

    θ' : {X : 𝓤 ̇ } (s' t' : S' X) → is-equiv (canonical-map ι' ρ' s' t')
    θ' {X} (s , a) (t , b) = γ
     where
      π : S' X → S X
      π (s , _) = s

      πem : is-embedding π
      πem = pr₁-embedding (axiomsXs✧ X)

      ξ : {s' t' : S' X} → is-equiv ( ap π {s'} {t'} )
      ξ {s'} {t'} = embedding-gives-ap-is-equiv π πem s' t'

      ℓ :  canonical-map ι' ρ' (s , a) (t , b) ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}
      ℓ ( refl (s , a) ) = refl (ρ (X , s) )

      e : is-equiv (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
      e = ∘-is-equiv (θ s t) ξ

      γ : is-equiv (canonical-map ι' ρ' (s , a) (t , b) )
      γ = equivs-closed-under-∼ e ℓ

  --with this MHE formulates and proves what `add-axioms` achieves: the characterization of the identity type remains the same, ignoring the axioms.
  characterization-of-≡-with-axioms : is-univalent 𝓤 → {S : 𝓤 ̇ → 𝓥 ̇ }
                                                    ( σ : SNS S 𝓣 )   ( axioms : (X : 𝓤 ̇) → S X → 𝓦 ̇ )
   →                                             ( (X : 𝓤 ̇) (s : S X) → is-subsingleton (axioms X s) )
   →                                             ( A 𝑩 : Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s )
                                                  ---------------------------------------------------
   →                                              (A ≡ 𝑩) ≃ ( [ A ] ≃[ σ ] [ 𝑩 ] )
  characterization-of-≡-with-axioms 𝓤★ σ axioms axiomsXs✧ = characterization-of-≡ 𝓤★ (add-axioms axioms axiomsXs✧ σ)
  --Recall, `characterization-of-≡ : is-univalent 𝓤 → { S : 𝓤 ̇ → 𝓥 ̇ } ( σ : SNS S 𝓦 ) → ( A 𝑩 : Σ S ) → ( A ≡ 𝑩 ) ≃ ( A ≃[ σ ] 𝑩 )`

------------------------------------------
--Magmas.
module magma-identity {𝓤 : Universe} where
  open uf-algebra-with-axioms

  Magma : 𝓤 ⁺ ̇
  Magma = Σ X ꞉ 𝓤 ̇ , (X → X → X) × is-set X

  _≅_ : Magma → Magma → 𝓤 ̇
  (X , _∙_ , _) ≅ (Y , _*_ , _) = Σ f ꞉ (X → Y) , is-equiv f  × ( ( λ x x' → f (x ∙ x') ) ≡ (λ x x' → f x * f x') )

  characterization-of-Magma-≡ : is-univalent 𝓤 → (A 𝑩 : Magma ) → (A ≡ 𝑩) ≃ (A ≅ 𝑩)
  characterization-of-Magma-≡ 𝓤★ = characterization-of-≡-with-axioms 𝓤★
    ∞-magma-identity.sns-data   ( λ X s → is-set X )   ( λ X s → being-set-is-subsingleton (univalence-gives-dfunext 𝓤★ ) )

  --"The above equivalence is characterized by induction on identifications as the function that maps reflexivity identification to the identity equivalence.
  characterization-of-characterization-of-Magma-≡ : (𝓤★ : is-univalent 𝓤) (A : Magma)
   →       ∣ characterization-of-Magma-≡ 𝓤★ A A ∣ (refl A)    ≡    ( 𝑖𝑑 ⟪ A ⟫ , id-is-equiv ⟪ A ⟫ , refl _ )
  characterization-of-characterization-of-Magma-≡ 𝓤★ A = refl _

--EXERCISE. Characterize identifications of monoids along the above lines.  It is convenient to redefine the type of monoids to an equivalent
-- type in the above format of structure with axioms. The following development solves this exercise.
-- !!! Come back to this later !!!

--------------------------------------------------
--Pointed types.
module pointed-type-identity {𝓤 : Universe} where

  Pointed : 𝓤 ̇ → 𝓤 ̇
  Pointed X = X

  sns-data : SNS Pointed 𝓤
  sns-data = (ι , ρ , θ)
   where
    ι : (A 𝑩 : Σ Pointed) → ⟨ A ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓤 ̇
    ι (X , x₀) (Y , y₀) (f , _) = (f x₀ ≡ y₀)

    ρ : (A : Σ Pointed) → ι A A (id-≃ ⟨ A ⟩)
    ρ (X , x₀) = refl x₀

    θ : {X : 𝓤 ̇} (x₀ x₁ : Pointed X) → is-equiv (canonical-map ι ρ x₀ x₁)
    θ x₀ x₁ = equivs-closed-under-∼ (id-is-equiv (x₀ ≡ x₁) ) h
     where
      h : canonical-map ι ρ x₀ x₁ ∼ 𝑖𝑑 (x₀ ≡ x₁)
      h (refl x₀) = refl (refl x₀)

  _≅_ : Σ Pointed → Σ Pointed → 𝓤 ̇
  (X , x₀) ≅ (Y , y₀) = Σ f ꞉ (X → Y) , is-equiv f × (f x₀ ≡ y₀)

  characterization-of-pointed-type-≡ :  is-univalent 𝓤 → (A 𝑩 : Σ Pointed)
                                                      ---------------------------------
   →                                                        (A ≡ 𝑩)   ≃   (A ≅ 𝑩)
  characterization-of-pointed-type-≡ 𝓤★ = characterization-of-≡ 𝓤★ sns-data

  --EXERCISE. This equivalence is characterized by induction on identifications as the function that maps reflexivity to the identity equivalence.
  --SOLUTION.
  characterization-of-characterization-of-pointed-type-≡ : (𝓤★ : is-univalent 𝓤) (A : Σ Pointed)
   →       ∣ characterization-of-pointed-type-≡ 𝓤★ A A ∣ (refl A)    ≡    ( 𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _ )
  characterization-of-characterization-of-pointed-type-≡ 𝓤★ A = refl _

------------------------------------------------------------------------------------------------------------------------
--Combining two mathematical structures.
{-"We now show how to join two mathematics structures so as to obtain a characterization of the identifications of the join from the
    characterization of the equalities of the structures. For example, we build the characterization of identifications of pointed ∞-magmas from
    the characterizations of the identifications of pointed types and the characterization of the identifications of magmas. Moreover, adding
    axioms, we get a characterization of identifications of monoids which amounts to the characterization of identifications of pointed ∞-magmas.
    Further adding an axiom, we get an automatic characterization of group identifications." -}

module uf-algebra-join where

  --MHE begins with the following technical lemma:
  technical-lemma : { X : 𝓤 ̇ } { A : X → X → 𝓥 ̇ } { Y : 𝓦 ̇ } { B : Y → Y → 𝓣 ̇ }
            (f : (x₀ x₁ : X) → x₀ ≡ x₁ → A x₀ x₁)     (g : (y₀ y₁ : Y) → y₀ ≡ y₁ → B y₀ y₁)
   →      ( (x₀ x₁ : X) → is-equiv ( f x₀ x₁ ) ) →  ( (y₀ y₁ : Y) → is-equiv ( g y₀ y₁ ) )
   →      ( z₀ z₁ : X × Y ) → is-equiv (λ ( z₀≡z₁ : z₀ ≡ z₁) → f (pr₁ z₀) (pr₁ z₁) (ap pr₁ z₀≡z₁) ,
                                                                                   g (pr₂ z₀) (pr₂ z₁) (ap pr₂ z₀≡z₁) )

  technical-lemma {𝓤} {𝓥} {𝓦}{𝓣} {X} {A} {Y} {B} f g feq geq ( x₀ , y₀ ) = γ
   where
    module _ (z₁ : X × Y) where
      x₁ = pr₁ z₁
      y₁ = pr₂ z₁

      r : (x₀ , y₀) ≡ (x₁ , y₁) → A x₀ x₁ × B y₀ y₁
      r p = f x₀ x₁ (ap pr₁ p) , g y₀ y₁ (ap pr₂ p)

      f' : (a : A x₀ x₁) → x₀ ≡ x₁
      f' = inverse (f x₀ x₁) (feq x₀ x₁)

      g' : (b : B y₀ y₁) → y₀ ≡ y₁
      g' = inverse (g y₀ y₁) (geq y₀ y₁)

      s :  A x₀ x₁ × B y₀ y₁ → ( x₀ , y₀ ) ≡ ( x₁ , y₁ )
      s (a , b) = to-×-≡ (f' a , g' b)

      η :  (c : A x₀ x₁ × B y₀ y₁) → r (s c) ≡ c
      η (a , b) =
        let f01 = f x₀ x₁ (ap pr₁ (to-×-≡ (f' a , g' b))) in
        let g01 = g y₀ y₁ (ap pr₂ (to-×-≡ (f' a , g' b))) in
          r (s (a , b))                                          ≡⟨ refl _ ⟩
          r ( to-×-≡  (f' a , g' b) )                        ≡⟨ refl _ ⟩
          ( f01 , g01 )                                        ≡⟨ ii ⟩
          ( f x₀ x₁ (f' a) ,  g y₀ y₁ (g' b) )            ≡⟨ iii ⟩
          a , b                                                  ∎
          where
            ii = ap₂ (λ p q → f x₀ x₁ p , g y₀ y₁ q) (ap-pr₁-to-×-≡ (f' a) (g' b) ) (ap-pr₂-to-×-≡ (f' a) (g' b) )

            iii : f x₀ x₁ (f' a) , g y₀ y₁ (g' b) ≡ a , b
            iii = to-×-≡ ( inverses-are-sections (f x₀ x₁) (feq x₀ x₁) a ,
                              inverses-are-sections (g y₀ y₁) (geq y₀ y₁) b )

    γ : ∀ z₁ → is-equiv (r z₁)
    γ = fiberwise-retractions-are-equivs ( λ z₁ → A x₀ (pr₁ z₁) × B y₀ (pr₂ z₁) )
              (x₀ , y₀) r (λ z₁ → (s z₁ , η z₁))

  --MHE then considers two structures specified by `S₀` and `S₁`, and works with structures specified by their combination `λ X → S₀ X × S₁ X`
  variable 𝓥₀ 𝓥₁ 𝓦₀ 𝓦₁ : Universe

  ⟪_⟫ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇} {S₁ : 𝓤 ̇ → 𝓥₁ ̇} → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → 𝓤 ̇
  ⟪ X , s₀ , s₁ ⟫ = X

  [_]₀ :  {S₀ : 𝓤 ̇ → 𝓥₀ ̇} {S₁ : 𝓤 ̇ → 𝓥₁ ̇} → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₀
  [ X , s₀ , s₁ ]₀ = (X , s₀)

  [_]₁ :  {S₀ : 𝓤 ̇ → 𝓥₀ ̇} {S₁ : 𝓤 ̇ → 𝓥₁ ̇} → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₁
  [ X , s₀ , s₁ ]₁ = (X , s₁)

  --MAIN CONSTRUCTION IN THIS SUBMODULE
  join :  {S₀ : 𝓤 ̇ → 𝓥₀ ̇} {S₁ : 𝓤 ̇ → 𝓥₁ ̇}
   →        SNS S₀ 𝓦₀    →    SNS S₁ 𝓦₁
          ------------------------------------------
   →      SNS (λ X → S₀ X × S₁ X) (𝓦₀ ⊔ 𝓦₁)

  join {𝓤} {𝓥₀}  {𝓥₁}  {𝓦₀} {𝓦₁} {S₀} {S₁} (ι₀ , ρ₀ , θ₀) (ι₁ , ρ₁ , θ₁)  = ι , ρ , θ
   where
     S : 𝓤 ̇ → 𝓥₀ ⊔ 𝓥₁ ̇
     S X = S₀ X × S₁ X

     ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦₀ ⊔ 𝓦₁ ̇
     ι A B cm∼c = ι₀ [ A ]₀ [ B ]₀ cm∼c × ι₁ [ A ]₁ [ B ]₁ cm∼c

     ρ : ( A : Σ S ) → ι A A ( id-≃ ⟨ A ⟩ )
     ρ A = ρ₀ [ A ]₀ , ρ₁ [ A ]₁

     θ : {X : 𝓤 ̇} (s t : S X) → is-equiv (canonical-map ι ρ s t)
     θ {X} (s₀ , s₁) (t₀ , t₁) = γ
      where
       c : (p : s₀ , s₁ ≡ t₀ , t₁) → ι₀ (X , s₀) (X , t₀) (id-≃ X) × ι₁ (X , s₁) (X , t₁) (id-≃ X)
       c p = canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) , canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p)

       ceq : is-equiv c
       ceq = technical-lemma (canonical-map ι₀ ρ₀) (canonical-map ι₁ ρ₁) θ₀ θ₁ (s₀ , s₁) (t₀ , t₁)

       cm∼c : canonical-map ι ρ (s₀ , s₁) (t₀ , t₁) ∼ c
       cm∼c (refl (s₀ , s₁)) = refl (ρ₀ (X , s₀) , ρ₁ (X , s₁))

       γ : is-equiv ( canonical-map ι ρ (s₀ , s₁)  (t₀ , t₁) )
       γ = equivs-closed-under-∼ ceq cm∼c

  --MHE then characterizes the identity type of structures in the join by the following relation:
  _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇}  {S₁ : 𝓤 ̇ → 𝓥₁ ̇}
   →             (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → SNS S₀ 𝓦₀ → SNS S₁ 𝓦₁
   →             (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
   →             𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇
  A ≃⟦ σ₀ , σ₁ ⟧ B = Σ f ꞉ ( ⟪ A ⟫ → ⟪ B ⟫ ) , Σ feq ꞉ is-equiv f ,
                                 UF-Algebra.homomorphic σ₀ [ A ]₀ [ B ]₀ (f , feq)  ×  UF-Algebra.homomorphic σ₁ [ A ]₁ [ B ]₁ (f , feq)

  --From this, the join construction, and the general structure identity principle, MHE proves,
  characterization-of-join-≡ : is-univalent 𝓤 → {S₀ : 𝓤 ̇ → 𝓥 ̇} {S₁ : 𝓤 ̇ → 𝓥₁ ̇}
              (σ₀ : SNS S₀ 𝓦₀)    (σ₁ : SNS S₁ 𝓦₁)    ( A B : Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X )
           ----------------------------------------------------------------------
    →                                     (A ≡ B) ≃ ( A ≃⟦ σ₀ , σ₁ ⟧ B )
  characterization-of-join-≡ 𝓤★ σ₀ σ₁ = characterization-of-≡ 𝓤★ (join σ₀ σ₁)

--"This concludes the `uf-algebra-join` submodule. Some examples of uses of this follow."

-----------------------------------------------------------------------------------------------
--Pointed ∞-magmas.
module pointed-∞-magma-identity {𝓤 : Universe} where
  open uf-algebra-join

  ∞-Magma∙ : 𝓤 ⁺ ̇
  ∞-Magma∙ = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

  _≅_ : ∞-Magma∙ → ∞-Magma∙ → 𝓤 ̇
  (X , _∙_ , x₀) ≅ (Y , _*_ , y₀)  =  Σ f ꞉ (X → Y) ,    is-equiv f
                                                                 ×   ( (λ x x' → f (x ∙ x') ) ≡ (λ x x' → f x * f x') )
                                                                 ×   (f x₀ ≡ y₀)

  characterization-of-pointed-magma-≡ : is-univalent 𝓤  →  (A B : ∞-Magma∙)
                                                      --------------------------------------
   →                                                            (A ≡ B)   ≃   (A ≅ B)
  characterization-of-pointed-magma-≡ 𝓤★ = characterization-of-join-≡ 𝓤★  ∞-magma-identity.sns-data   pointed-type-identity.sns-data

  --EXERCISE. This equivalence is characterized by induction on identifications as the function that maps reflexivity to the identity equivalence.
  --SOLUTION.
  characterization-of-characterization-of-pointed-magma-≡ : (𝓤★ : is-univalent 𝓤) (A : ∞-Magma∙)
   →     ∣ characterization-of-pointed-magma-≡ 𝓤★ A A ∣ (refl A)   ≡  ( 𝑖𝑑 ⟪ A ⟫ , id-is-equiv ⟪ A ⟫ , refl _ , refl _ )
  characterization-of-characterization-of-pointed-magma-≡ 𝓤★ A = refl _

-----------------------------------------------------------------------------------
--Monoids. (combining joins and addition of axioms)
module monoid-identity {𝓤 : Universe} (𝓤★ : is-univalent 𝓤) where
  open import UF-Monoid using (left-neutral; right-neutral; associative)
  open uf-algebra-join
  open uf-algebra-with-axioms

  dfe : dfunext 𝓤 𝓤
  dfe = univalence-gives-dfunext 𝓤★

  monoid-structure : 𝓤 ̇ → 𝓤 ̇
  monoid-structure X = (X → X → X) × X

  monoid-axioms : (X : 𝓤 ̇) → monoid-structure X → 𝓤 ̇
  monoid-axioms X ( _·_ , e ) = is-set X   ×   left-neutral e _·_  ×   right-neutral e _·_  ×  associative _·_

  Monoid : 𝓤 ⁺ ̇
  Monoid = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ monoid-structure X , monoid-axioms X s

  monoid-axioms-subsingleton : (X : 𝓤 ̇) (s : monoid-structure X)
   →                                is-subsingleton (monoid-axioms X s)
  monoid-axioms-subsingleton X ( _·_ , e ) s = γ s
    where
      Xset : is-set X
      Xset = pr₁ s

      γ : is-subsingleton ( monoid-axioms X ( _·_ , e ) )
      γ = ×-is-subsingleton (being-set-is-subsingleton dfe)
                ( ×-is-subsingleton
                    ( Π-is-subsingleton dfe ( λ x → Xset (e · x) x ) )
                    ( ×-is-subsingleton
                        ( Π-is-subsingleton dfe ( λ x → Xset (x · e) x) )
                        ( Π-is-subsingleton dfe
                            ( λ x → Π-is-subsingleton dfe ( λ y → Π-is-subsingleton dfe ( λ z → Xset ( (x · y) · z ) ( x · (y · z) ) ) ) )
                        )
                    )
                )

  sns-data : SNS ( λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s ) 𝓤
  sns-data = add-axioms
                    monoid-axioms   monoid-axioms-subsingleton
                    ( join  ∞-magma-identity.sns-data   pointed-type-identity.sns-data )   --   SNS S 𝓣

  _≅_ : Monoid → Monoid → 𝓤 ̇
  ( X , ( _∙_ , d ) , _ ) ≅ ( Y , ( _*_ , e ) , _ ) =
          Σ f ꞉ (X → Y) , is-equiv f
                             × ( (λ x x' → f (x ∙ x') ) ≡ (λ x x' → f x * f x') )
                             × (f d ≡ e)

  characterization-of-monoid-≡ : is-univalent 𝓤 → (A B : Monoid)
                                               ------------------------------
   →                                                   (A ≡ B) ≃ (A ≅ B)
  characterization-of-monoid-≡ 𝓤★ = characterization-of-≡ 𝓤★ sns-data

  --EXERCISE. This equivalence is characterized by induction on identifications as the function that maps reflexivity to the identity equivalence.
  characterization-of-characterization-of-monoid-≡ : (𝓤★ : is-univalent 𝓤) (A : Monoid)
   →     ∣ characterization-of-monoid-≡ 𝓤★ A A ∣ (refl A)   ≡  ( 𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _ , refl _  )
  characterization-of-characterization-of-monoid-≡ 𝓤★ A = refl _

----------------------------------------
-- Associative ∞-magmas.
{-"In the absence of the requirement that the underlying type is a set, the equivalences in the characterization of equality of associative
   ∞-magmas not only have to be homomorphic with respect to the magma operations but also need to respect the associativity data. -}

module associative-∞-magma-identity {𝓤 : Universe} {𝓤★ : is-univalent 𝓤} where

  fe : dfunext 𝓤 𝓤
  fe = univalence-gives-dfunext 𝓤★

  associative : {X : 𝓤 ̇} → (X → X → X) → 𝓤 ̇
  associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)

  ∞-amagma-structure : 𝓤 ̇ → 𝓤 ̇
  ∞-amagma-structure X = Σ _·_ ꞉ (X → X → X) , ( associative _·_ )

  ∞-aMagma : 𝓤 ⁺ ̇
  ∞-aMagma = Σ X ꞉ 𝓤 ̇ , ∞-amagma-structure X

  homomorphic : {X Y : 𝓤 ̇} → (X → X → X) → (Y → Y → Y) → (X → Y) → 𝓤 ̇
  homomorphic _·_ _*_ f = ( λ x y → f (x · y) ) ≡ ( λ x y → f x * f y )

  --"The notion of preservation of the associativity data depends not only on the homomorphism `f`, but also on the homomorphism data `h` for `f`:
  respect-assoc : {X A : 𝓤 ̇} ( _·_ : X → X → X ) (_*_ : A → A → A)
   →                   associative _·_ → associative _*_ → (f : X → A)
   →                   homomorphic _·_ _*_ f → 𝓤 ̇

  respect-assoc _·_ _*_ α β f h =   fα ≡ βf
   where
    ℓ : (x y z : domain f) →  f ( (x · y) · z) ≡ (f x * f y) * f z
    ℓ = λ x y z → f ( (x · y) · z)    ≡⟨ ap (λ - → - (x · y) z) h ⟩
                         f (x · y) * f z    ≡⟨ ap (λ - → - x y * f z ) h ⟩
                         (f x * f y) * f z  ∎

    r : (x y z : domain f) →  f ( x · (y · z)) ≡ f x * (f y * f z)
    r = λ x y z → f ( x · (y · z) )    ≡⟨ ap (λ - → - x (y · z) ) h ⟩
                         f  x * f (y · z)    ≡⟨ ap (λ - → f x * - y z) h ⟩
                         f x * (f y * f z)  ∎

    fα βf : ∀ x y z → (f x * f y) * f z ≡ f x * (f y * f z)
    fα x y z = (f x * f y) * f z   ≡⟨ ( ℓ x y z ) ⁻¹ ⟩
                    f ( (x · y) · z)     ≡⟨ ap f (α x y z) ⟩  f ( x · (y · z))     ≡⟨ r x y z ⟩
                    f x * (f y * f z)  ∎
    βf x y z = β (f x) (f y) (f z)

  --"The functions `ℓ` and `r`, defined from the binary homomorphism condition `h`, give the homomorphism condition for the two
  -- induced ternary magma operations of each magma. The following, which holds by construction, will be used implicitly:
  remark : {X : 𝓤 ̇} (_·_ : X → X → X) (α β : associative _·_ )
   →         respect-assoc _·_ _·_ α β id (refl _·_)  ≡  ( (λ x y z → refl ( (x · y) · z) ∙ ap id (α x y z) ) ≡ β)
  remark _·_ α β = refl _

  --"The homomorphism condition `ι` is then defined as expected and the reflexivity condition `ρ` relies on the above remark.

  sns-data : SNS ∞-amagma-structure 𝓤
  sns-data = ( ι , ρ , θ )
   where
    ι : (𝑿 𝑨 : ∞-aMagma) → ⟨ 𝑿 ⟩ ≃ ⟨ 𝑨 ⟩ → 𝓤 ̇
    ι ( X , _·_ , α ) ( A , _*_ , β ) ( f , _ ) = Σ h ꞉ homomorphic _·_ _*_ f , respect-assoc _·_ _*_ α β f h

    ρ : (𝑿 : ∞-aMagma) → ι 𝑿 𝑿 (id-≃ ⟨ 𝑿 ⟩ )
    ρ (X , _·_ , α) = h , p
     where
      h : homomorphic _·_ _·_ id
      h = refl _·_

      p : (λ x y z → refl ( (x · y) · z) ∙ ap id (α x y z) ) ≡ α
      p = fe ( λ x → fe ( λ y → fe ( λ z → refl-left ∙ ap-id (α x y z) ) ) )  --  Recall, `refl-left : ... {p : x ≡ y} → refl x ∙ p ≡ p`
                                                                                                -- and  `ap-id : ... (p : x ≡ y)→ ap id p ≡ p
    --"We prove the canonicity condition `θ` with the Yoneda machinery.
    θ : {X : 𝓤 ̇} (s t : ∞-amagma-structure X) → is-equiv (canonical-map ι ρ s t)
    θ {X} s = universal-fiberwise-equiv (λ t → ι (X , s) (X , t) (id-≃ X) )
                          (∃!t X s) s (canonical-map ι ρ s)

       -- !!!come back to this!!! (yet to fully comprehend this use of "the Yoneda machinery") 
       where
         ∃!t : (X : 𝓤 ̇) → ∀ s → ∃! t ꞉ ∞-amagma-structure X , ι (X , s) (X , t) (id-≃ X)
         ∃!t X (_·_ , α) = c , φ
           where
             c : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X)
             c = (_·_ , α) , ρ (X , _·_ , α)

             φ : (σ : Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X) ) → c ≡ σ
             φ ( (_·_ , β) , refl _·_ , k) = γ
               where
                     a : associative _·_
                     a x y z = refl ( (x · y) · z ) ∙ ap id (α x y z)

                     g : singleton-type' a → Σ t ꞉ ∞-amagma-structure X , ι (X , _·_ , α) (X , t) (id-≃ X)
                     g (β , k) = (_·_ , β) , refl _·_ , k

                     sta✧ : is-subsingleton (singleton-type' a)
                     sta✧ = singletons-are-subsingletons _ (singleton-types'-are-singletons _ a)

                     q : α , pr₂ (ρ (X , _·_ , α) ) ≡ β , k
                     q = sta✧ _ _

                     γ : c ≡ (_·_ , β) , refl _·_ , k
                     γ = ap g q

  --"The promised characterization of associative ∞-magma equality then follows directly from the general structure of identity principle:
  _≅_ : ∞-aMagma → ∞-aMagma → 𝓤 ̇
  ( X , _·_ , α )  ≅  ( Y , _*_ , β ) = Σ f ꞉ (X → Y)
                                                    , is-equiv f
                                                    × (Σ h ꞉ homomorphic _·_ _*_ f
                                                              , respect-assoc _·_ _*_ α β f h)

  characterization-of-∞-aMagma-≡ : (A B : ∞-aMagma) → (A ≡ B) ≃ (A ≅ B)
  characterization-of-∞-aMagma-≡ = characterization-of-≡ 𝓤★ sns-data

--------------------------------------------------
-- Groups. "We add an axiom to monoids to get groups."
module group-identity {𝓤 : Universe} (𝓤★ : is-univalent 𝓤) where
  hfe : hfunext 𝓤 𝓤
  hfe = univalence-gives-hfunext 𝓤★

  open uf-algebra-with-axioms
  open monoid-identity {𝓤} 𝓤★ hiding (sns-data ; _≅_)

  group-structure : 𝓤 ̇ → 𝓤 ̇
  group-structure X = Σ s ꞉ monoid-structure X , monoid-axioms X s

  group-axiom : (X : 𝓤 ̇) → monoid-structure X → 𝓤 ̇
  group-axiom X (_·_ , e) = (x : X) → Σ x' ꞉ X , (x · x' ≡ e) × (x' · x ≡ e)

  Group : 𝓤 ⁺ ̇
  Group = Σ X ꞉ 𝓤 ̇ , Σ ( (_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

  inv-lemma : (X : 𝓤 ̇) (_·_ : X → X → X) (e : X)
   →          monoid-axioms X (_·_ , e)
   →          (x y z : X)   →   (y · x) ≡ e    →   (x · z) ≡ e
               ------------------------------------------
   →                              y ≡ z

  inv-lemma X _·_ e (Xset , lneut , rneut , assoc) x y z q p =
      y   ≡⟨ (rneut y)⁻¹ ⟩      ( y · e )
          ≡⟨ ap (y ·_) (p ⁻¹) ⟩  ( y · (x · z) )
          ≡⟨ (assoc y x z)⁻¹ ⟩  ( (y · x) · z )
          ≡⟨ ap (_· z) q ⟩       ( e · z )
          ≡⟨ lneut z ⟩           z                       ∎

  group-axiom-is-subsingleton : (X : 𝓤 ̇) → (s : group-structure X) → is-subsingleton ( group-axiom X (pr₁ s) )
  group-axiom-is-subsingleton X ( (_·_ , e) , (Xset , lneut , rneut , assoc) ) = Π-is-subsingleton dfe ΣX✧
   where
     ΣX✧ : (x : X) → is-subsingleton (Σ x' ꞉ X , (x · x' ≡ e) × (x' · x ≡ e) )
     ΣX✧ x (y , _ , q) (z , p , _) = to-subtype-≡ (λ x' → ×-is-subsingleton (Xset (x · x') e) (Xset (x' · x) e) ) y≡z
       where
         y≡z : y ≡ z
         y≡z = inv-lemma X _·_ e (Xset , lneut , rneut , assoc) x y z q p

  sns-data : SNS (λ X → Σ s ꞉ group-structure X , group-axiom X (pr₁ s) ) 𝓤
  sns-data = add-axioms (λ X s → group-axiom X (pr₁ s) ) group-axiom-is-subsingleton (monoid-identity.sns-data 𝓤★)

  _≅_ : Group → Group → 𝓤 ̇
  (X , ( (_·_ , d) , _ ) , _ ) ≅ (Y , ( (_*_ , e) , _) , _) =
    Σ f ꞉ (X → Y) , is-equiv f
                      × ( (λ x x' → f (x · x') ) ≡  (λ x x' → f x * f x') )
                      × (f d ≡ e)

  characterization-of-group-≡ : (A B : Group) → (A ≡ B) ≃ (A ≅ B)
  characterization-of-group-≡ = characterization-of-≡ 𝓤★ sns-data

  --EXERCISE. This equivalence is characterized by induction on identifications as the function that maps reflexivity to the identity equivalence.
  -- SOLUTION.
  characterization-of-characterization-of-group-≡ : (𝓤★ : is-univalent 𝓤) (A : Group)
   →     ∣ characterization-of-group-≡ A A ∣ (refl A)   ≡  ( 𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _ , refl _  )
  characterization-of-characterization-of-group-≡ 𝓤★ A = refl _

--EXERCISE. In the case of groups, as opposed to monoids, the preservation of the unit follows from the preservation of the
-- multiplication, and hence one can remove `f d ≡ e` from the above definition. Prove that `(A ≅ B) ≃ (A ≅' B)` and hence,
-- by transitivity, `(A ≡ B) ≃ (A ≅' B)` where
  _≅'_ : Group → Group → 𝓤 ̇
  (X , ( (_·_ , d) , _) , _) ≅' (Y , ( (_*_ , e) , _) , _) =
    Σ f ꞉ (X → Y) , is-equiv f
                     × ( (λ x x' → f (x · x') ) ≡ (λ x x' → f x * f x' ) )

  --"We now solve this exercise and do a bit more on the way. We first name various projections and introduce notation.
  group-structure-of : (G : Group) → group-structure ⟨ G ⟩
  group-structure-of (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = (_·_ , e) , Xset , lneut , rneut , assoc

  monoid-structure-of : (G : Group) → monoid-structure ⟨ G ⟩
  monoid-structure-of (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = (_·_ , e)

  monoid-axioms-of : (G : Group) → monoid-axioms ⟨ G ⟩ (monoid-structure-of G)
  monoid-axioms-of (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = Xset , lneut , rneut , assoc

  multiplication : (G : Group) → ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  multiplication (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = _·_

  syntax multiplication G x y = x ·⟨ G ⟩ y

  unit : (G : Group) → ⟨ G ⟩
  unit (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = e

  group-is-set : (G : Group)  →   is-set ⟨ G ⟩
  group-is-set (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = Xset

  unit-left : (G : Group) (x : ⟨ G ⟩) → unit G ·⟨ G ⟩ x ≡ x
  unit-left (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) x = lneut x

  unit-right : (G : Group) (x : ⟨ G ⟩) → x ·⟨ G ⟩ unit G ≡ x
  unit-right (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) x = rneut x

  assoc : (G : Group) (x y z : ⟨ G ⟩ )
   →   (x ·⟨ G ⟩ y) ·⟨ G ⟩ z ≡ x ·⟨ G ⟩ (y ·⟨ G ⟩ z)
  assoc (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) = assoc

  inv : (G : Group) → ⟨ G ⟩  → ⟨ G ⟩
  inv (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) x = pr₁ (gpax x)

  inv-left inv-is-left-inv : (G : Group) (x : ⟨ G ⟩) → inv G x ·⟨ G ⟩ x ≡ unit G
  inv-is-left-inv (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) x = pr₂ (pr₂ (gpax x) )
  inv-left = inv-is-left-inv -- alias

  inv-right inv-is-right-inv : (G : Group) (x : ⟨ G ⟩) → x ·⟨ G ⟩ inv G x ≡ unit G
  inv-is-right-inv (X , ( (_·_ , e) , Xset , lneut , rneut , assoc) , gpax) x = pr₁ (pr₂ (gpax x))
  inv-right = inv-is-right-inv -- alias

  --"We now solve the exercise.
  preserves-multiplication : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
  preserves-multiplication G H f = (λ (x y : ⟨ G ⟩) → f ( x ·⟨ G ⟩ y ) ) ≡ ( λ (x y : ⟨ G ⟩) → f  x ·⟨ H ⟩ f y )

  preserves-unit : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
  preserves-unit G H f = f (unit G) ≡ unit H

  idempotent-is-unit : (G : Group) (x : ⟨ G ⟩) → x ·⟨ G ⟩ x ≡ x
                                         -----------------------------
   →                                            x ≡ unit G
  idempotent-is-unit (G) x x-is-idemp = γ
    where
      x' = inv G x
      e = unit G
      γ =   x                           ≡⟨  (unit-right G x) ⁻¹ ⟩
              x ·⟨ G ⟩ e                ≡⟨ (ap (λ - → x ·⟨ G ⟩ -) (inv-right G x))⁻¹ ⟩
              x ·⟨ G ⟩ (x ·⟨ G ⟩ x')    ≡⟨ (assoc G x x x')⁻¹ ⟩
              ( x ·⟨ G ⟩ x ) ·⟨ G ⟩ x'  ≡⟨ ap (λ - → - ·⟨ G ⟩ x') x-is-idemp ⟩
              x ·⟨ G ⟩ x'                ≡⟨ inv-right G x ⟩
              e                           ∎

  unit-preservation-lemma : (G H : Group)
                               ( f : ⟨ G ⟩ → ⟨ H ⟩ )    →    preserves-multiplication G H f
                             -------------------------------------------------------
   →                                        preserves-unit G H f

  unit-preservation-lemma G H f f-pres-mult = idempotent-is-unit H (f e) fe-is-idemp
    where
      e = unit G

      fe-is-idemp : (f e) ·⟨ H ⟩ (f e) ≡ f e
      fe-is-idemp =
        (f e) ·⟨ H ⟩ (f e)       ≡⟨ ap (λ - → - e e) f-pres-mult ⁻¹ ⟩
        f (e ·⟨ G ⟩ e)     ≡⟨ ap f (unit-left G e) ⟩
        f e                   ∎

  --"If a map preverves multiplication then it also preserves inverses:
  inv-unique : (G : Group) (x y z : ⟨ G ⟩)
   →             (y ·⟨ G ⟩ x) ≡ unit G   →    (x ·⟨ G ⟩ z) ≡ unit G
               ------------------------------------------------
   →                                    y ≡ z
  inv-unique G = inv-lemma ⟨ G ⟩ (multiplication G) (unit G) (monoid-axioms-of G)

  left-inv-unique : (G : Group) (x x' : ⟨ G ⟩) → (x' ·⟨ G ⟩ x) ≡ unit G → x' ≡ inv G x
  left-inv-unique G x x' x'x≡e = inv-unique G x x' (inv G x) x'x≡e (inv-right G x)

  right-inv-unique : (G : Group) (x x' : ⟨ G ⟩) → (x ·⟨ G ⟩ x') ≡ unit G → x' ≡ inv G x
  right-inv-unique G x x' xx'≡e = (inv-unique G x (inv G x) x' (inv-left G x) xx'≡e)⁻¹

  preserves-inv : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
  preserves-inv G H f = (x : ⟨ G ⟩) → f (inv G x) ≡ inv H (f x)

  inv-preservation-lemma : (G H : Group)
                   (f : ⟨ G ⟩ → ⟨ H ⟩)   →    preserves-multiplication G H f
                  ---------------------------------------------------
   →                    preserves-inv G H f

  inv-preservation-lemma G H f f-pres-mult x = γ
   where
    ξ : f (inv G x) ·⟨ H ⟩ (f x) ≡ unit H
    ξ = f (inv G x) ·⟨ H ⟩ (f x)     ≡⟨ (ap (λ - → - (inv G x) x) f-pres-mult)⁻¹ ⟩
          f (inv G x ·⟨ G ⟩ x)        ≡⟨ ap f (inv-is-left-inv G x) ⟩
          f (unit G)                    ≡⟨ unit-preservation-lemma G H f f-pres-mult ⟩
          unit H                        ∎

    ζ : (f x) ·⟨ H ⟩ inv H (f x) ≡ unit H
    ζ = inv-is-right-inv H (f x)

    γ : f (inv G x) ≡ inv H (f x)
    γ = inv-unique H (f x) ( f (inv G x) ) ( inv H (f x) ) ξ ζ

  --"The usual notion of group homomorphism is that of multiplication-preserving function. But this is known to be equivalent to our
  -- chosen notion, which reflects the way we constructed groups from monoids and by our general structure identity principle.
  is-homomorphism : (G H : Group) → (⟨ G ⟩ → ⟨ H ⟩) → 𝓤 ̇
  is-homomorphism G H f = preserves-multiplication G H f × preserves-unit G H f

  preservation-of-mult-is-subsingleton : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
   →                     is-subsingleton (preserves-multiplication G H f)
  preservation-of-mult-is-subsingleton G H f = pmult✧
   where
    pmult✧ : is-subsingleton (preserves-multiplication G H f)
    pmult✧ = Π-is-set hfe
            ( λ _ → Π-is-set hfe ( λ _ → group-is-set H ) )
            ( λ (x y : ⟨ G ⟩ ) → f (x ·⟨ G ⟩ y) )  ( λ (x y : ⟨ G ⟩) → f x ·⟨ H ⟩ f y)

  being-hom-is-subsingleton : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
   →                     is-subsingleton (is-homomorphism G H f)
  being-hom-is-subsingleton G H f = hom✧
   where
    punit✧ : is-subsingleton (preserves-unit G H f)
    punit✧ = (group-is-set H (f (unit G) ) (unit H) )

    hom✧ : is-subsingleton (is-homomorphism G H f)
    hom✧ = ×-is-subsingleton (preservation-of-mult-is-subsingleton G H f) punit✧

  notions-of-homomorphism-agree : (G H : Group) (f : ⟨ G ⟩ → ⟨ H ⟩)
   →                     is-homomorphism G H f ≃ preserves-multiplication G H f
  notions-of-homomorphism-agree G H f = logically-equivalent-subsingletons-are-equivalent _ _
    (being-hom-is-subsingleton G H f) (preservation-of-mult-is-subsingleton G H f) (α , β)
      where
        α : is-homomorphism G H f → preserves-multiplication G H f
        α = pr₁

        β : preserves-multiplication G H f → is-homomorphism G H f
        β f-pres-mult = f-pres-mult , unit-preservation-lemma G H f f-pres-mult

  ≅-agreement : (G H : Group) → (G ≅ H) ≃ (G ≅' H)
  ≅-agreement G H = Σ-cong ( λ f → Σ-cong ( λ _ → notions-of-homomorphism-agree G H f) )

  --"This equivalence is that which forgets the preservation of the unit:
  forget-unit-preservation : (G H : Group) → (G ≅ H) → (G ≅' H)
  forget-unit-preservation G H (f , e , m , _) = f , e , m

  NB : (G H : Group) → ∣ ≅-agreement G H ∣ ≡ forget-unit-preservation G H
  NB G H = refl _

  forget-unit-preservation-is-equiv : (G H : Group) → is-equiv (forget-unit-preservation G H)
  forget-unit-preservation-is-equiv G H = ∥ ≅-agreement G H ∥

  --"This completes the solution of the exercise."                                         ∎

------------------------------------------------------
-- Subgroups.
{-"It is common mathematical practice to regard isomorphic groups to be the same, which is a theorem in univalent mathematics, with the
   notion of sameness articulated by the identity type, as shown above. However, for some purposes, we may wish to consider two groups
   to be the same if they have the same elements. For example, in order to show that the subgroups of a group form an algebraic lattice
   with the finitely generated subgroups as the compact elements, it is this notion of equality that is used, with subgroup containment as
   the lattice order.

  "Asking whether two groups have the same elements in univalent mathematics doesn't make sense unless they are subgroups of the same
   ambient group.  In the same way that in univalent mathematics two members of the powerset are equal iff they have the same elements,
   two subgroups are equal if and only if they have the same elements. This can be formulated and proved in two equivalent ways.

     1. A subgroup is an element of the powerset of the underlying set of the group that is closed under the group operations.  So the
        type of subgroups of a given group is embedded as a subtype of the powerset of the underlying set and hence inherits the
        characterization of equality from the powerset.

     2. A subgroup of a group `G` is a group `H` *together* with a homomorphic embedding `H → G`. With this second  definition, two
        subgroups `H` and `H'` are equal iff the embeddings `H → G` and `H' → G` can be completed to a commutative triangle by a
        group isomorphism `H → H'`, which is necessarily unique when it exists (cf. the discussion of equality in slice types below."  -}

module subgroup-identity (𝓤 : Universe) (𝓤★ : Univalence) where

 gfe : global-dfunext
 gfe = univalence-gives-global-dfunext 𝓤★
 open monoid-identity {𝓤} (𝓤★ 𝓤) hiding (sns-data ; _≅_)
 open group-identity {𝓤} (𝓤★ 𝓤)

 --"We assume an arbitrary ambient group `G` in the following discussion.
 module ambient (G : Group) where

  _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  x · y = x ·⟨ G ⟩ y

  infixl 42 _·_

  --"We abbreviate 'closed under the group operations' by `group-closed`:
  group-closed : ( ⟨ G ⟩ → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
  group-closed 𝓐 = 𝓐 (unit G) × ( ( x y : ⟨ G ⟩ ) → 𝓐 x → 𝓐 y → 𝓐 (x · y) )
                                             × ( ( x : ⟨ G ⟩ ) → 𝓐 x → 𝓐 (inv G x) )

  --The collection of subgroups of a group G is defined here to be the collection of all subsets A : 𝓟 ⟨ G ⟩ for which 
  -- we have proof that A is closed under the group operations (really that consists of three (sub)proofs).
  Subgroups : 𝓤 ⁺ ̇
  Subgroups = Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed ( _∈ A )

  --the carrier of a given subgroup
  ⟪_⟫ : Subgroups → 𝓟 ⟨ G ⟩
  ⟪ A , _ , _ , _ ⟫ = A

  being-group-closed-subset-is-subsingleton : ( A : 𝓟 ⟨ G ⟩ ) → is-subsingleton ( group-closed ( _∈ A ) )
  being-group-closed-subset-is-subsingleton A =
    ×-is-subsingleton (∈-is-subsingleton A (unit G))
    ( ×-is-subsingleton
       ( Π-is-subsingleton dfe
         ( λ x → Π-is-subsingleton dfe
         ( λ y → Π-is-subsingleton dfe
         ( λ _ → Π-is-subsingleton dfe
         ( λ _ → ∈-is-subsingleton A (x · y) ) ) ) ) )
       ( Π-is-subsingleton dfe
         ( λ x → Π-is-subsingleton dfe
         ( λ _ → ∈-is-subsingleton A (inv G x) ) ) ) )

  ⟪⟫-is-embedding : is-embedding ⟪_⟫
  ⟪⟫-is-embedding = pr₁-embedding being-group-closed-subset-is-subsingleton

  --"Therefore equality of subgroups is equality of their underlying subsets in the powerset:
  ap-⟪⟫ : (S T : Subgroups) → S ≡ T → ⟪ S ⟫ ≡ ⟪ T ⟫
  ap-⟪⟫ S T = ap ⟪_⟫

  ap-⟪⟫-is-equiv : (S T : Subgroups) → is-equiv (ap-⟪⟫ S T)
  ap-⟪⟫-is-equiv = embedding-gives-ap-is-equiv ⟪_⟫ ⟪⟫-is-embedding

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set S T = equiv-to-subsingleton
                                            ( ap-⟪⟫ S T , ap-⟪⟫-is-equiv S T )
                                            ( powersets-are-sets' 𝓤★ ⟪ S ⟫ ⟪ T ⟫ )

  --[Here are some useful lemmas extracted from MHE's proof of `subgroup-equality` for clarity.]
  subgroup-equality-gives-membership-equiv : (S T : Subgroups)   --[called `f` in MHE's proof]
   →                                  S ≡ T
                        -----------------------------------
   →                   (x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫
  subgroup-equality-gives-membership-equiv S T S≡T x =
    transport (λ - → x ∈ ⟪ - ⟫) S≡T , transport (λ - → x ∈ ⟪ - ⟫) (S≡T ⁻¹)

  membership-equiv-gives-carrier-equality :   (S T : Subgroups)   --[called `h` in MHE's proof]
   →                   ( (x : ⟨ G ⟩ ) →  x ∈ ⟪ S ⟫  ⇔  x ∈ ⟪ T ⟫ )
                        -----------------------------------------
   →                                   ⟪ S ⟫ ≡ ⟪ T ⟫
  membership-equiv-gives-carrier-equality S T φ = subset-extensionality' 𝓤★ α β
    where
      α : ⟪ S ⟫ ⊆ ⟪ T ⟫
      α x = lr-implication (φ x)

      β : ⟪ T ⟫ ⊆ ⟪ S ⟫
      β x = rl-implication (φ x)

  --[This lemma is called `g` in MHE's proof of `subgroup-equality`]
  membership-equiv-gives-subgroup-equality :   (S T : Subgroups)
   →                   ( ( x : ⟨ G ⟩ ) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫ )
                         ---------------------------------------
   →                                       S ≡ T
  membership-equiv-gives-subgroup-equality S T =
    inverse ( ap-⟪⟫ S T) (ap-⟪⟫-is-equiv S T) ∘ (membership-equiv-gives-carrier-equality S T)

  membership-equiv-is-subsingleton :  (S T : Subgroups)  →  is-subsingleton ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫)
  membership-equiv-is-subsingleton S T =
   Π-is-subsingleton dfe ( λ x → ×-is-subsingleton
                                      (Π-is-subsingleton dfe  ( λ _ → ∈-is-subsingleton ⟪ T ⟫ x ) )
                                      (Π-is-subsingleton dfe  ( λ _ → ∈-is-subsingleton ⟪ S ⟫ x ) )
                                  ) 

  --"It follows that two subgroups are equal if and only if they have the same elements:
  subgroup-equality :  (S T : Subgroups)
   →          ( S ≡ T )    ≃    ( ( x : ⟨ G ⟩ )  → ( x ∈ ⟪ S ⟫ ) ⇔ ( x ∈ ⟪ T ⟫ ) )

  subgroup-equality S T =
    logically-equivalent-subsingletons-are-equivalent _ _
      (subgroups-form-a-set S T) (membership-equiv-is-subsingleton S T)
      (subgroup-equality-gives-membership-equiv S T , membership-equiv-gives-subgroup-equality S T)


  --[wjd added]-------------------------------------------------------------------------------------
  --The converse of `membership-equiv-gives-carrier-equality` is obvious.
  carrier-equality-gives-membership-equiv :   (S T : Subgroups)
   →                            ⟪ S ⟫ ≡ ⟪ T ⟫
                  ----------------------------------------
   →              ( ( x : ⟨ G ⟩ ) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫ )
  carrier-equality-gives-membership-equiv S T (refl _) x = id , id

  --so we have...
  carrier-equiv :   (S T : Subgroups)    →   ( ( x : ⟨ G ⟩ ) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫ )    ≃      ( ⟪ S ⟫ ≡ ⟪ T ⟫ )
  carrier-equiv S T = logically-equivalent-subsingletons-are-equivalent _ _
    ( membership-equiv-is-subsingleton S T )  ( powersets-are-sets' 𝓤★ ⟪ S ⟫ ⟪ T ⟫ )
    ( membership-equiv-gives-carrier-equality S T , carrier-equality-gives-membership-equiv S T )

  --...which yields an alternative subgroup equality lemma.
  subgroup-equality' :  (S T : Subgroups)   →   ( S ≡ T )    ≃   ( ⟪ S ⟫ ≡ ⟪ T ⟫ )
  subgroup-equality' S T =
   (S ≡ T)                                                         ≃⟨ subgroup-equality S T ⟩
   ( ( x : ⟨ G ⟩ )  → ( x ∈ ⟪ S ⟫ ) ⇔ ( x ∈ ⟪ T ⟫ ) )  ≃⟨ carrier-equiv S T ⟩
   (⟪ S ⟫ ≡ ⟪ T ⟫)                                            ■
  --------------------------------------------------------------------------------------------------


  --"As an application of the subtype classifier, we now show that the type of subgroups is equivalent to the type
  -- `Σ H ꞉ Group , Σ f ꞉ (⟨ H ⟩ → ⟨ G ⟩) , is-embedding f × is-homomorphism H G f`

  --Following MHE, we introduce notation for the type of group structures satisfying the group axioms.
  --(though we use 𝔾 where MHE uses T)
  𝔾 : 𝓤 ̇ → 𝓤 ̇
  𝔾 X = Σ ( (_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e)

  --"We use an anonymous module to give common assumptions for the following few lemmas:
  module _ {X : 𝓤 ̇} (h : X → ⟨ G ⟩ ) (hem : is-embedding h) where
    private
     h-lc : left-cancellable h
     h-lc = embeddings-are-lc h hem

    having-group-closed-fiber-is-subsingleton : is-subsingleton ( group-closed (fiber h) )
    having-group-closed-fiber-is-subsingleton = being-group-closed-subset-is-subsingleton (λ x → (fiber h x , hem x) )

    at-most-one-homomorphic-structure : is-subsingleton (Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h )
    at-most-one-homomorphic-structure
      ( ( ( ( _*_ , unitH ) , maxioms ) , gaxiom) , (pmult , punit) )
      ( ( ( ( _*'_ , unitH' ) , maxioms' ) , gaxiom') , (pmult' , punit') ) = γ
     where
      τ τ' : 𝔾 X
      τ = ( ( _*_ , unitH ) , maxioms ) , gaxiom
      τ' = ( ( _*'_ , unitH' ) , maxioms' ) , gaxiom'

      τhom : is-homomorphism (X , τ) G h
      τhom = (pmult , punit)

      τ'hom : is-homomorphism (X , τ') G h
      τ'hom = (pmult' , punit')

      p : _*_ ≡ _*'_
      p = gfe (λ x → gfe (λ y →
              h-lc ( h ( x * y )   ≡⟨ ap (λ - → - x y ) pmult ⟩
                       h x · h y     ≡⟨ (ap (λ - → - x y) pmult')⁻¹ ⟩
                       h ( x *' y)     ∎ ) ) )

      q : unitH ≡ unitH'
      q = h-lc ( h unitH  ≡⟨ punit ⟩
                     unit G   ≡⟨ punit' ⁻¹ ⟩
                     h unitH'  ∎)

      r : (_*_ , unitH) ≡ (_*'_ , unitH')
      r = to-×-≡ (p , q)

      τ≡τ' : τ ≡ τ'
      τ≡τ' = to-subtype-≡ (group-axiom-is-subsingleton X) (to-subtype-≡ (monoid-axioms-subsingleton X) r)

      γ : (τ , τhom) ≡ (τ' , τ'hom)
      γ = to-subtype-≡ (λ τ → being-hom-is-subsingleton (X , τ) G h) τ≡τ'

    group-closed-fiber-gives-homomorphic-structure : group-closed (fiber h)
     →                         (Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h)
    group-closed-fiber-gives-homomorphic-structure (unitc , mulc , invc) = τ , hhom
      where
        hfib : (x : X) → fiber h (h x)
        hfib x = x , refl (h x)

        unitH : X
        unitH = fiber-point unitc

        _*_ : X → X → X
        x * y = fiber-point ( mulc (h x) (h y) (hfib x) (hfib y) )

        invH : X → X
        invH x = fiber-point ( invc (h x) (hfib x) )

        pmul : (x y : X) → h (x * y) ≡ h x · h y
        pmul x y = fiber-identification (mulc (h x) (h y) (hfib x) (hfib y) )

        punit : h unitH ≡ unit G
        punit = fiber-identification unitc

        pinv : (x : X) → h (invH x) ≡ inv G (h x)
        pinv x = fiber-identification (invc (h x) (hfib x) )

        unitH-left : (x : X) → unitH * x ≡ x
        unitH-left x = h-lc (
               h (unitH * x)    ≡⟨ pmul unitH x ⟩
               h unitH · h x   ≡⟨ ap (λ - → - · (h x)) punit ⟩
               unit G · h x     ≡⟨ unit-left G (h x) ⟩
               h x                ∎ )

        unitH-right : (x : X) → x * unitH ≡ x
        unitH-right x = h-lc (
          h (x * unitH)   ≡⟨ pmul x unitH ⟩
          h x · h unitH   ≡⟨ ap (λ - → (h x) · -) punit ⟩
          h x · unit G    ≡⟨ unit-right G (h x) ⟩
          h x                ∎ )

        assocH : (x y z : X) → ( (x * y) * z ) ≡ ( x * (y * z ) )
        assocH x y z = h-lc (
          h ( ( x * y ) * z )   ≡⟨ pmul (x * y) z ⟩
          h ( x * y ) · h z    ≡⟨ ap (λ - → - · (h z)) (pmul x y) ⟩
          ( h x · h y ) · h z  ≡⟨ assoc G (h x) (h y) (h z) ⟩
          h x · (h y · h z)  ≡⟨ ap (λ - → (h x) · -) (pmul y z)⁻¹ ⟩
          h  x · h ( y * z )   ≡⟨ ( pmul x (y * z) )⁻¹ ⟩
          h  ( x * ( y * z ) )  ∎ )

        group-axiomH : (x : X) → Σ x' ꞉ X , (x * x' ≡ unitH) × (x' * x ≡ unitH)
        group-axiomH x = invH x ,

             h-lc ( h ( x * invH x )     ≡⟨ pmul x (invH x) ⟩
                     h x · h ( invH x )   ≡⟨ ap (λ - → (h x) · -) (pinv x) ⟩
                     h x · inv G (h x)    ≡⟨ inv-right G (h x) ⟩
                     unit G                ≡⟨ punit ⁻¹ ⟩
                     h unitH               ∎ ) ,

             h-lc ( h ( invH x * x )     ≡⟨ pmul (invH x) x ⟩
                     h ( invH x ) ·  h x   ≡⟨ ap (λ - → - · (h x)) (pinv x) ⟩
                     inv G (h x) · h x    ≡⟨ inv-left G (h x) ⟩
                     unit G                ≡⟨ punit ⁻¹ ⟩
                     h unitH               ∎ )

        Xset : is-set X
        Xset = subtypes-of-sets-are-sets h h-lc (group-is-set G)

        τ : 𝔾 X
        τ = ( ( _*_ , unitH ) , ( Xset , unitH-left , unitH-right , assocH ) ) , group-axiomH

        hhom : is-homomorphism (X , τ) G h
        hhom = gfe (λ x → gfe (pmul x) ) , punit

    homomorphic-structure-gives-group-closed-fiber : (Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h)
     →                                                                                group-closed (fiber h)
    homomorphic-structure-gives-group-closed-fiber
      ( ( ( ( _*_ , unitH) , maxioms) , gaxiom) , (pmult , punit) ) = unitc , mulc , invc
        where
          H : Group
          H = X , ( (_*_ , unitH) , maxioms) , gaxiom

          unitc : fiber h (unit G)
          unitc = unitH , punit

          mulc : ( ( x y : ⟨ G ⟩ ) → fiber h x → fiber h y → fiber h (x · y) )
          mulc x y ( a , ha≡x ) ( b , hb≡y ) = (a * b) ,
              (h (a * b)       ≡⟨ ap (λ - → - a b)  pmult ⟩
              (h a) · (h b)    ≡⟨ ap (λ - → - · (h b)) ha≡x ⟩
              x · (h b)        ≡⟨ ap (λ - → x · -) hb≡y ⟩
              x · y             ∎)

          invc : ( ( x : ⟨ G ⟩ ) → fiber h x → fiber h (inv G x) )
          invc x (a , ha≡x) = inv H a ,
            ( h (inv H a) ≡⟨ inv-preservation-lemma H G h pmult a ⟩
             inv G (h a)  ≡⟨ ap (inv G) ha≡x ⟩
             inv G x      ∎ )

    --"What is important for our purposes is this:
    fiber-structure-lemma : group-closed (fiber h) ≃ (Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h)
    fiber-structure-lemma = logically-equivalent-subsingletons-are-equivalent _ _
                                        having-group-closed-fiber-is-subsingleton
                                        at-most-one-homomorphic-structure
                                        (group-closed-fiber-gives-homomorphic-structure ,
                                         homomorphic-structure-gives-group-closed-fiber)

  --"This is the end of the anonymous submodule and we can now prove the desired result. We apply the material on the subtype classifier.
  characterization-of-the-type-of-subgroups :
       Subgroups     ≃     ( Σ H ꞉ Group  ,  Σ h ꞉ ( ⟨ H ⟩ → ⟨ G ⟩ ) ,  is-embedding h × is-homomorphism H G h )

  characterization-of-the-type-of-subgroups =
   Subgroups                                                                                                                      ≃⟨ i ⟩
   ( Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A) )                                                                               ≃⟨ ii ⟩
   ( Σ (X , h , e) ꞉ Subtypes ⟨ G ⟩ , group-closed (fiber h) )                                                          ≃⟨ iii ⟩
   ( Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , group-closed (fiber h) )                                                    ≃⟨ iv ⟩
   ( Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h )                              ≃⟨ v ⟩
   ( Σ X ꞉ 𝓤 ̇ , Σ h  ꞉ (X → ⟨ G ⟩ ) , Σ e ꞉ is-embedding h , Σ τ ꞉ 𝔾 X , is-homomorphism (X , τ) G h )  ≃⟨ vi ⟩
   ( Σ X ꞉ 𝓤 ̇ , Σ h  ꞉ (X → ⟨ G ⟩ ) , Σ τ ꞉ 𝔾 X , Σ e ꞉ is-embedding h , is-homomorphism (X , τ) G h )  ≃⟨ vii ⟩
   ( Σ X ꞉ 𝓤 ̇ , Σ τ ꞉ 𝔾 X , Σ h  ꞉ (X → ⟨ G ⟩ ) , is-embedding h × is-homomorphism (X , τ) G h )        ≃⟨ viii ⟩
   ( Σ H ꞉ Group  ,  Σ h ꞉ ( ⟨ H ⟩ → ⟨ G ⟩ ) ,  is-embedding h × is-homomorphism H G h )                   ■
    where
     φ : Subtypes ⟨ G ⟩ → 𝓟 ⟨ G ⟩
     φ = χ-special is-subsingleton ⟨ G ⟩

     φeq : is-equiv φ
     φeq = χ-special-is-equiv (𝓤★ 𝓤) gfe is-subsingleton ⟨ G ⟩

     i = id-≃ Subgroups
     ii = Σ-change-of-variable (λ (A : 𝓟 ⟨ G ⟩) → group-closed (_∈ A) ) φ φeq
     iii = Σ-assoc
     iv = Σ-cong (λ X → Σ-cong ( λ (h , e) → fiber-structure-lemma h e) )
     v = Σ-cong λ X → Σ-assoc
     vi = Σ-cong λ X → Σ-cong ( λ h → Σ-flip) 
     vii = Σ-cong λ X → Σ-flip
     viii = ≃-sym Σ-assoc

  --"In particular, a subgroup induces a genuine group, which is homomorphically embedded into the ambient group.
  induced-group : Subgroups → Group
  induced-group S = pr₁ (∣ characterization-of-the-type-of-subgroups ∣ S)

--------------------------------------------------------
-- The slice type.
module slice-identity {𝓤 𝓥 : Universe} (R : 𝓥 ̇) where

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → R
 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = ( ι , ρ , θ )
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , g) (Y , h) (f , _) = (g ≡ h ∘ f)

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩ )
   ρ (X , g) = refl g

   cme : {X : 𝓤 ̇} {g h : S X} → canonical-map ι ρ g h ∼ 𝑖𝑑 ( g ≡ h )
   cme (refl g) = refl (refl g) 

   θ : {X : 𝓤 ̇} (g h : S X) → is-equiv (canonical-map ι ρ g h)
   θ g h = equivs-closed-under-∼ (id-is-equiv (g ≡ h) ) cme

--"*Exercise*. The above equivalence is characterized by induction on identifications as the function that maps the reflexive
-- identification to the identity equivalence.
--"*Exercise.* Apply the ideas of this section to characterize equality of the type `Σ H ꞉ Group , Σ f ꞉ (⟨ H ⟩ → ⟨ G ⟩) ,
-- is-embedding f × is-homomorphism H G f` as discussed in the section on subgroup equality."

