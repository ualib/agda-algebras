--FILE: UF-Algebra.agda
--BLAME: williamdemeo@gmail.com
--DATE: 21 Apr 2020
--UPDATE: 29 May 2020
--REF: Much of this file is based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
--SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sip 
--      In particular, the quoted comments below, along with sections of code to which those comments refer, are due to Martin Escardo.
--      Throughout, MHE = Martin Hötzel Escardo.

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Prelude using (Universe; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; _⁺; _̇;_⊔_; universe-of; id; 𝑖𝑑; _∘_; _,_; Σ; -Σ; pr₁; pr₂; Π; -Π; domain; _×_; _≡_; refl; _∼_; transport; _≡⟨_⟩_; _∎; ap; _∙_; _⁻¹; _⇔_; _iff_; lr-implication; rl-implication; 𝟘; 𝟚; ∣_∣; ∥_∥)

open import UF-Equality using (refl-left; ap-id; _◁_; singleton-type'; singleton-types'-are-singletons; _≃_;  id-≃; is-equiv; id-is-equiv; Σ-≡-≃; Σ-cong; ≃-sym; _≃⟨_⟩_; _■; ∘-is-equiv; inverse; to-×-≡; ap-pr₁-to-×-≡; ap-pr₂-to-×-≡; inverses-are-sections; fiber; fiber-point; fiber-identification; Σ-flip)

open import UF-Singleton using (is-set; is-singleton; is-subsingleton; singletons-are-subsingletons)

open import UF-Extensionality using (∃!; -∃!; being-set-is-subsingleton; univalence-gives-dfunext; dfunext; Π-is-subsingleton; hfunext; univalence-gives-hfunext; Π-is-set; Univalence; global-dfunext; univalence-gives-global-dfunext; 𝓟; _∈_; ∈-is-subsingleton; powersets-are-sets'; _⊆_; subset-extensionality; subset-extensionality')

open import UF-Univalence using (is-univalent; Id→Eq; Σ-assoc; equivs-closed-under-∼; ap₂; ×-is-subsingleton; to-subtype-≡; logically-equivalent-subsingletons-are-equivalent; equiv-to-subsingleton; left-cancellable; subtypes-of-sets-are-sets; Σ-change-of-variable; transport-ap-≃)

open import UF-Embedding using (transport-lemma; fiberwise-equiv-universal; universal-fiberwise-equiv; fiberwise-equiv-criterion; fiberwise-equiv-criterion'; fiberwise-retractions-are-equivs; is-embedding; pr₁-embedding; embedding-gives-ap-is-equiv; embeddings-are-lc; _↪_; Subtypes; χ-special; χ-special-is-equiv)

-------------------------------------------------------------------------------------------------
--"A structure identity principle for a standard notion of structure"
module UF-Algebra where

{-Following Martin Hötzel Escardo (MHE), op. cit., we consider mathematical structures specified by a *structure function*
    `S : 𝓤 ̇ → 𝓥 ̇`
  and we consider types `X : 𝓤` equipped with structure `s : S X`, collected in the type `Σ X ꞉ 𝓤 , S X` (or `Σ S` for short).
  For example, a magma---a structure with a single binary operation---would have `𝓥 = 𝓤` and `S X = X → X → X`.
  So the structure map specifies gives the structure's signature, that is, its operations and their arities.

  MHE describes the identity type `Id (Σ S) 𝑨 𝑩`, in "favourable circumstances", in terms of equivalences of the underlying
  types `⟨ 𝑨 ⟩` and `⟨ 𝑩 ⟩` of the structures `𝑨 𝑩 : Σ S`.
-}

--the underlying universe (aka "carrier") of the strucutre
⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
⟨ X , _ ⟩ = X

--the image of the structure map (aka the "signature") of the structure
structure : {S : 𝓤 ̇ → 𝓥 ̇} (𝑨 : Σ S) → S ⟨ 𝑨 ⟩
structure ( _ , s ) = s

--we use the following alias for the signature of a structure
⟦_⟧ : {S : 𝓤 ̇ → 𝓥 ̇} (𝑨 : Σ S) → S ⟨ 𝑨 ⟩
⟦ _ , s ⟧ = s  -- alias for `structure`    ( NOTATION: type ⟦ and ⟧ with `\[[` and `\]]` )

{-The "favorable circumstances" according to MHE are the following:

      * `ι : (𝑨 𝑩 : Σ S) → ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓦 ̇` describes equivalences (which turn out to be the homs)
      * `ρ : (𝑨 : Σ S) → ι 𝑨 𝑨 (id-≃ ⟨ 𝑨 ⟩)`          stipulates that all identity equivalences are homomorphisms.

   MHE also requires that two structures on the same type making the identity equivalence a homomorphism must be identified in a
   canonical way.   Accordingly, we have the canonical map `s ≡ t  → ι (X , s) (X , t) (id-≃ X)`, defined by induction on identifications
   by `refl s ↦ ρ (X , s)`, and this map must be an equivalence for all `X : 𝓤` and `s t : S X`.
-}
canonical-map : {S : 𝓤 ̇ → 𝓥 ̇}  ( ι : ( 𝑨 𝑩 : Σ S ) → ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓦 ̇ )
                                                ( ρ : ( 𝑨 : Σ S ) → ι 𝑨 𝑨 ( id-≃ ⟨ 𝑨 ⟩ ) )
                                                { X : 𝓤 ̇ }      ( s t : S X )
                                             ---------------------------------------
 →                                           s ≡ t   →   ι ( X , s ) ( X , t ) ( id-≃ X )

canonical-map ι ρ {X} s s ( refl s ) = ρ ( X , s )

--MHE captures these data in a type which represents a "standard notion of structure" (SNS).
SNS : ( 𝓤 ̇ → 𝓥 ̇) → ( 𝓦 : Universe ) → 𝓤 ⁺ ⊔ 𝓥 ⊔ ( 𝓦 ⁺ ) ̇

SNS {𝓤}{𝓥} S 𝓦 = Σ ι ꞉ ( ( 𝑨 𝑩 : Σ S ) → ( ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓦 ̇ ) ) ,
                                 Σ ρ ꞉ ( ( 𝑨 : Σ S ) → ι 𝑨 𝑨 ( id-≃ ⟨ 𝑨 ⟩ ) ) ,
                                        ( { X : 𝓤 ̇} ( s t : S X ) → is-equiv ( canonical-map ι ρ s t ) )

{- An inhabitant of `SNS S 𝓦` is thus a triple, `( ι , ρ , θ )`, where `ι` and `ρ` are as described above and
    `θ : ( s t : S X ) → is-equiv ( canonical-map ι ρ s t ) )`  says that the canonical-map is an equivalence (i.e., has singleton fibers).

   Recall,  `is-equiv f = (y : codomain f) → is-singleton (fiber f y) )`
   So, `is-equiv (canonical-map ...)` means all the fibers of the canonical map are singletons, and, recall, having only singleton
   fibers translates to having singleton kernel blocks, i.e., injective... or maybe an embedding (?)    -}

--Following MHE, we use the label `homomorphic` for the first projection of SNS.
homomorphic : { S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
                 -------------------------------------
 →               ( 𝑨 𝑩 : Σ S ) → ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓦 ̇
homomorphic  ( ι , _ , _ )  = ι

{- For example, suppose
        `S : 𝓤 ̇ → 𝓥 ̇` is  a magma structure map,
        `𝑨 𝑩 : Σ S` are two magmas,
        `σ : SNS S 𝓦`,
        `f : ⟨ 𝑨 ⟩ → ⟨ 𝑩 ⟩` is an equivalence, and
        `feq : is-equiv f` is a proof that f is an equivalence.
   Then, `homomorphic σ 𝑨 𝑩 (f , feq)` asserts that `f` is a magma homomorphism from 𝑨 to 𝑩. -}

--Homomorphic equivalences of `𝑨 𝑩 : Σ S`, witnessed by `σ : SNS S 𝓦`, are collected in a type:
_≃[_]_ : { S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇
𝑨 ≃[ σ ] 𝑩 = Σ f ꞉ ( ⟨ 𝑨 ⟩ → ⟨ 𝑩 ⟩ ) ,                     -- ∃ a map f from carrier of 𝑨 to carrier of 𝑩;
                      Σ feq ꞉ is-equiv f ,                          -- f has singleton fibers, and so
                           homomorphic σ 𝑨 𝑩 ( f , feq )      -- f is a homomorphism from 𝑨 to 𝑩.
--infix 20 _≈[_]_

--If `𝑨 𝑩 : Σ S` are structures and `𝑨 ≡ 𝑩`, then `𝑨 ≃[ σ ] 𝑩`.
Id→homEq : { S : 𝓤 ̇ → 𝓥 ̇ } ( σ : SNS S 𝓦 )
 →               ( 𝑨 𝑩 : Σ S )   →    𝑨 ≡ 𝑩
                 -----------------------------
 →                          𝑨 ≃[ σ ] 𝑩

Id→homEq (_ , ρ , _) 𝑨 𝑨 ( refl 𝑨 ) =  ( id , id-is-equiv ⟨ 𝑨 ⟩  , ρ 𝑨 )

--With this, MHE proves the promised characterization of identity on Σ S:
homomorphism-lemma : { S : 𝓤 ̇ → 𝓥 ̇ }   ( σ : SNS S 𝓦 )   ( 𝑨 𝑩 : Σ S )    ( p : ⟨ 𝑨 ⟩ ≡ ⟨ 𝑩 ⟩ )
 →               ( transport S p ⟦ 𝑨 ⟧ ≡ ⟦ 𝑩 ⟧ ) ≃ homomorphic σ 𝑨 𝑩 (Id→Eq ⟨ 𝑨 ⟩ ⟨ 𝑩 ⟩ p )

homomorphism-lemma ( ι , ρ , θ ) ( X , s ) ( X , t ) ( refl X ) = γ
 where
  γ :  (s ≡ t) ≃ ι ( X , s ) ( X , t ) ( id-≃ X )
  γ = canonical-map ι ρ s t , θ s t

--(paraphrasing MHE) Assuming univalence, we have an identification between equivalences `≡` and `≃[ σ ]`
--(a manifestation of the notion that isomorphic objects are the same).
characterization-of-≡ : is-univalent 𝓤   →   { S : 𝓤 ̇ → 𝓥 ̇ }
                                 ( σ : SNS S 𝓦 )   →   ( 𝑨 𝑩 : Σ S )
                               ----------------------------------
 →                               ( 𝑨 ≡ 𝑩 )   ≃   ( 𝑨 ≃[ σ ] 𝑩 )
characterization-of-≡ 𝓤★ {S} σ 𝑨 𝑩 =
   (𝑨 ≡ 𝑩)                                                                   ≃⟨ i ⟩
   ( Σ p ꞉ ⟨ 𝑨 ⟩ ≡ ⟨ 𝑩 ⟩ , transport S p ⟦ 𝑨 ⟧ ≡ ⟦ 𝑩 ⟧ )    ≃⟨ ii ⟩
   ( Σ p ꞉ ⟨ 𝑨 ⟩ ≡ ⟨ 𝑩 ⟩ , ι 𝑨 𝑩 ( Id→Eq ⟨ 𝑨 ⟩ ⟨ 𝑩 ⟩ p ) ) ≃⟨ iii ⟩
   ( Σ e ꞉ ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ , ι 𝑨 𝑩 e )                                 ≃⟨ iv ⟩
   ( 𝑨 ≃[ σ ] 𝑩 )                                                           ■
  where
      ι = homomorphic σ
      i = Σ-≡-≃ 𝑨 𝑩
      ii = Σ-cong (homomorphism-lemma σ 𝑨 𝑩)
      iii = ≃-sym (Σ-change-of-variable (ι 𝑨 𝑩) (Id→Eq ⟨ 𝑨 ⟩ ⟨ 𝑩 ⟩ ) (𝓤★ ⟨ 𝑨 ⟩ ⟨ 𝑩 ⟩) )
      iv = Σ-assoc

--MHE next observes that the above equivalence is pointwise equal to `Id→homEq`, so `Id→homEq` is itself an equivalence.
Id-homEq-is-equiv : (𝓤★ : is-univalent 𝓤) { S : 𝓤 ̇ → 𝓥 ̇ }
                             ( σ : SNS S 𝓦 )   →   ( 𝑨 𝑩 : Σ S )
                            ----------------------------------
 →                         is-equiv ( Id→homEq σ 𝑨 𝑩 )

Id-homEq-is-equiv 𝓤★ {S} σ 𝑨 𝑩 = γ
   where
    h : (𝑨 𝑩 : Σ S) → Id→homEq σ 𝑨 𝑩 ∼ ∣ characterization-of-≡ 𝓤★ σ 𝑨 𝑩 ∣
    h  𝑨 𝑨 (refl 𝑨) = refl _

    γ : is-equiv (Id→homEq σ 𝑨 𝑩)
    γ = equivs-closed-under-∼ ( ∥ characterization-of-≡ 𝓤★ σ 𝑨 𝑩 ∥ ) ( h 𝑨 𝑩 )

--Finally, MHE gives a characterization of the canonical map and of when it is an equivalence, applying Yoneda.
module _ { S : 𝓤 ̇ → 𝓥 ̇}
             ( ι : ( 𝑨 𝑩 : Σ S ) → ⟨ 𝑨 ⟩ ≃ ⟨ 𝑩 ⟩ → 𝓦 ̇ )
             ( ρ : ( ( 𝑨 : Σ S ) → ι 𝑨 𝑨 ( id-≃ ⟨ 𝑨 ⟩ ) ) )
             {X : 𝓤 ̇}  where

  canonical-map-charac : ( s t : S X ) ( s≡t : s ≡ t )
   →   ( canonical-map ι ρ s t s≡t )    ≡    ( transport ( λ - → ι ( X , s ) ( X , - ) ( id-≃ X ) ) s≡t ( ρ ( X , s ) ) )

  canonical-map-charac s = transport-lemma ( λ t → ι (X , s) (X , t) (id-≃ X) ) s (canonical-map ι ρ s)

  when-canonical-map-is-equiv :
    ( (s t : S X) → is-equiv ( canonical-map ι ρ s t ) )  ⇔  ( (s : S X) → ∃! t ꞉ S X , ι (X , s) (X , t) (id-≃ X) )

  when-canonical-map-is-equiv = ( λ e s → fiberwise-equiv-universal (A s) s (τ s) (e s) ) ,
                                               ( λ φ s → universal-fiberwise-equiv (A s) (φ s) s (τ s) )
    where
      A = λ s t → ι (X , s) (X , t) (id-≃ X)
      τ = canonical-map ι ρ

   --It suffices to have any equivalence for the canonical map to be an equivalence:
  canonical-map-equiv-criterion :
             ( (s t : S X) → (s ≡ t) ≃ ι (X , s) (X , t) (id-≃ X) )
           ---------------------------------------------
   →        (s t : S X)  →  is-equiv (canonical-map ι ρ s t)

  canonical-map-equiv-criterion φ s =
     fiberwise-equiv-criterion' (λ t → ι (X , s) (X , t) (id-≃ X) ) s (φ s) (canonical-map ι ρ s)

  --In fact, it suffices to have any retraction for the canonical map to be an equivalence:
  canonical-map-equiv-criterion' :
            ( (s t : S X) → ι (X , s) (X , t) (id-≃ X)  ◁  (s ≡ t) )
            ----------------------------------------------
   →       (s t : S X)   →  is-equiv (canonical-map ι ρ s t)

  canonical-map-equiv-criterion' φ s =
     fiberwise-equiv-criterion (λ t → ι (X , s) (X , t) (id-≃ X) ) s (φ s) (canonical-map ι ρ s)

