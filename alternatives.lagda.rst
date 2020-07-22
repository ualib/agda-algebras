.. FILE: alternatives.agda
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 19 Jul 2020
.. UPDATE: 19 Jul 2020

.. _alternatives:

=====================
Alternatives
=====================

Here we collect some of the possible alternative implementation choices for reference and for comparison with the one's we have chosen for use in the agda-ualib_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import prelude
  open import basic using (Signature; Algebra; Op; _̂_)
  open import homomorphisms using (hom; is-homomorphism; 𝒾𝒹)
  open import terms using (Term; _̇_; generator; node; comm-hom-term; 𝑻)
  open import congruences using (transitive; ker; ker-pred;
   Rel; 𝟎; con; _//_; Con; compatible-fun)

  open import Relation.Unary using (⋂)

  module alternatives {S : Signature 𝓞 𝓥} where

--------------------------------------

.. _homomorphisms intensionally:

Homomorphisms intensionally
---------------------------

Our implementation of the notion of homomorphisms in the agda-ualib is an extensional one. In :numref:`types for homomorphisms` we defined what it means for an operation 𝑓, interpreted in the algebras 𝑨 and 𝑩, to commute with a function :math:`g : A → B`. Recall,

.. code-block:: agda

   op_interpreted-in_and_commutes-with :
    (𝑓 : ∣ 𝑆 ∣) (𝑨 : Algebra 𝓤 𝑆) (𝑩 : Algebra 𝓦 𝑆)
    (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

   op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-with g =
    ∀( 𝒂 : ∥ 𝑆 ∥ 𝑓 → ∣ 𝑨 ∣ ) → g ((𝑓 ̂ 𝑨) 𝒂) ≡ (𝑓 ̂ 𝑩) (g ∘ 𝒂)

which of course says that for every tuple 𝒂 of ∥ 𝑆 ∥ 𝑓 elements from ∣ 𝑨 ∣, we have g (𝑓 ̂ 𝑨)𝒂 ≡ (𝑓 ̂ 𝑩)(g ∘ 𝒂).

An alternative, *intensional* notion of homomorphism might define the commuting of 𝑓 and g as follows:

::

  --intensional preservation of operations
  op_interpreted-in_and_commutes-intensionally-with :
   (𝑓 : ∣ S ∣) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with g =
   g ∘ (𝑓 ̂ 𝑨)  ≡ (λ 𝒂 → (𝑓 ̂ 𝑩) (g ∘ 𝒂))

Here we have used an equality that is intensional with respect to 𝒂, but extensional with respect to 𝑓.


::

  all-ops-in_and_commute-intensionally-with :
   (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  all-ops-in 𝑨 and 𝑩 commute-intensionally-with g =
   ∀(𝑓 : ∣ S ∣) → op 𝑓 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with g

  intensional-hom : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
   →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  intensional-hom 𝑨 𝑩 g =
   all-ops-in 𝑨 and 𝑩 commute-intensionally-with g

  Hom : Algebra 𝓦 S → Algebra 𝓤 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  Hom 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
   all-ops-in 𝑨 and 𝑩 commute-intensionally-with g


Full intensionality
~~~~~~~~~~~~~~~~~~~~~~

::

  -- intensional with respect to both 𝑓 and 𝒂)
  preserves-ops : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
   →              (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  preserves-ops (A , 𝐹ᴬ)(B , 𝐹ᴮ) g =
   (λ (𝑓 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝑓 → A) → g (𝐹ᴬ 𝑓 𝒂))
    ≡ (λ (𝑓 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝑓 → A )  → 𝐹ᴮ 𝑓 (g ∘ 𝒂))

  all-ops-in_and_commute-fully-intensionally-with :
   (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)
   (g : ∣ 𝑨 ∣  → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  all-ops-in 𝑨 and 𝑩 commute-fully-intensionally-with g =
   preserves-ops 𝑨 𝑩 g

  --the type of (intensional) homomorphisms
  HOM : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇

  HOM 𝑨 𝑩 = Σ g ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣) ,
             all-ops-in 𝑨 and 𝑩 commute-fully-intensionally-with g

------------------------------------

Alternative hom images
--------------------------

::

  module _ {A B : Algebra 𝓤 S} (h : hom A B)  where

   HomImage : ∣ B ∣ → 𝓤 ̇
   HomImage = λ b → Image ∣ h ∣ ∋ b

   hom-image : 𝓤 ̇
   hom-image = Σ (Image_∋_ ∣ h ∣)

   fres : ∣ A ∣ → Σ (Image_∋_ ∣ h ∣)
   fres a = ∣ h ∣ a , im a

   hom-image-alg : Algebra 𝓤 S
   hom-image-alg = hom-image , ops-interp
    where
     a : {f : ∣ S ∣ }(x : ∥ S ∥ f → hom-image) → ∥ S ∥ f → ∣ A ∣
     a x y = Inv ∣ h ∣  ∣ x y ∣ ∥ x y ∥

     ops-interp : (f : ∣ S ∣) → Op (∥ S ∥ f) hom-image
     ops-interp =
      λ f x → (∣ h ∣  (∥ A ∥ f (a x)) , im (∥ A ∥ f (a x)))


  _is-hom-image-of_ : (B : Algebra (𝓤 ⁺) S)
   →                  (A : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

  B is-hom-image-of A = Σ θ ꞉ (Rel ∣ A ∣ _) ,
                          con A θ  × ((∣ A ∣ // θ) ≡ ∣ B ∣)

  HomImagesOf : (Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  HomImagesOf A = Σ B ꞉ (Algebra _ S) , B is-hom-image-of A

  HomImagesOf-pred : (Algebra 𝓤 S)
   →                 Pred (Algebra ( 𝓤 ⁺ ) S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))

  HomImagesOf-pred A = λ B → B is-hom-image-of A

  _is-hom-image-of-class_ : {𝓤 : Universe} → (Algebra (𝓤 ⁺) S)
   →                        (Pred (Algebra 𝓤 S) (𝓤 ⁺))
   →                        𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

  B is-hom-image-of-class 𝒦 = Σ A ꞉ (Algebra _ S) ,
                                 (A ∈ 𝒦) × (B is-hom-image-of A)

  HomImagesOfClass : {𝓤 : Universe}
   →                 Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

  HomImagesOfClass 𝒦 = Σ B ꞉ (Algebra _ S) ,
                          (B is-hom-image-of-class 𝒦)

  H : {𝓤 : Universe} → Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
  H 𝒦 = HomImagesOfClass 𝒦

  -- Here ℒ𝒦 represents a (universe-indexed) collection of classes.
  H-closed : (ℒ𝒦 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
   →         (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)
   →          𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇

  H-closed ℒ𝒦 =
   λ 𝓤 B → (B is-hom-image-of-class (ℒ𝒦 𝓤)) → (B ∈ (ℒ𝒦 (𝓤 ⁺)))

  _≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
  A ≅ B =  Σ ϕ ꞉ (hom A B) , Σ ψ ꞉ (hom B A) ,
            (∣ ϕ ∣ ∘ ∣ ψ ∣ ≡ ∣ 𝒾𝒹 B ∣) × (∣ ψ ∣ ∘ ∣ ϕ ∣ ≡ ∣ 𝒾𝒹 A ∣)

  is-algebra-iso : {A B : Algebra 𝓤 S} (ϕ : hom A B) → 𝓤 ⁺ ̇
  is-algebra-iso {𝓤}{A} ϕ = ker ∣ ϕ ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

  AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
  AlgebraIsos {𝓤} A B = Σ ϕ ꞉ (hom A B) ,
                          is-algebra-iso {𝓤} {A} {B} ϕ

  _≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
  A ≈ B = is-singleton (AlgebraIsos A B)



--------------------------------------------

Alternative subuniverses
---------------------------

Recall, the `subuniverses module`_ of agda-ualib_ starts with a definition of the collection of subuniverses of an algebra A.  Since a subuniverse is a subset of the domain of A, it is defined as a predicate on ∣ A ∣.  Thus, the collection of subuniverses is a predicate on predicates on ∣ A ∣.

::

  Subuniverses : (A : Algebra 𝓤 S)
   →             Pred (Pred ∣ A ∣ 𝓣) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓣)

  Subuniverses (A , FA) B =
   (f : ∣ S ∣)(a : ∥ S ∥ f → A) → Im a ⊆ B → FA f a ∈ B

Next we could have defined a data type that represents the property of being a subuniverse. (Note that, in order to keep ``A`` at same universe level as ``Σ B , F``, we force ``B`` to live in the same universe.  We need to do this so that both ``A`` and ``Σ B , F`` can be classified by the same predicate ``SClo``.)

::

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

We could also have constructed an algebra with universe derived from the subuniverse data type.

::

  module _
   {A : Algebra 𝓤 S} {B : Pred ∣ A ∣ 𝓤}
   {F : (f : ∣ S ∣) → Op (∥ S ∥ f) (Σ B)}
   (B∈SubA : B ∈ Subuniverses A) where

   SubunivAlg : Algebra 𝓤 S
   SubunivAlg =
    Σ B , λ f x → ∥ A ∥ f (∣_∣ ∘ x) , B∈SubA f (∣_∣ ∘ x)(∥_∥ ∘ x)

   subuniv-to-subalg : SubunivAlg is-subalgebra-of A
   subuniv-to-subalg = mem B ∥ SubunivAlg ∥ λ f a → (refl _)


.. _the intensional-hom-image module:

The intensional-hom-image module
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The image of an intensional HOM is a subuniverse. (N.B. the proof still requires function extensionality. Question: Is it necessary?)

::

  module intensional-hom-image
   {A B : Algebra 𝓤 S} (h : HOM A B)  where

   HOMImage : ∣ B ∣ → 𝓤 ̇
   HOMImage = λ b → Image ∣ h ∣ ∋ b

   HOM-image : 𝓤 ̇
   HOM-image = Σ (Image_∋_ ∣ h ∣)

   fres' : ∣ A ∣ → Σ (Image_∋_ ∣ h ∣)
   fres' a = ∣ h ∣ a , im a

   HOM-image-alg : Algebra 𝓤 S
   HOM-image-alg = HOM-image , ops-interp
    where
     a : {f : ∣ S ∣} (x : ∥ S ∥ f → HOM-image) (y : ∥ S ∥ f)
      →  ∣ A ∣
     a x y = Inv ∣ h ∣  ∣ x y ∣ ∥ x y ∥

     ops-interp : ( f : ∣ S ∣ ) → Op (∥ S ∥ f) HOM-image
     ops-interp = λ f x →(∣ h ∣ (∥ A ∥ f (a x)) , im (∥ A ∥ f (a x)))

   HOM-image-is-sub : funext 𝓥 𝓤 → HOMImage ∈ Subuniverses B
   HOM-image-is-sub fe f b b∈Imh = eq (∥ B ∥ f b) (∥ A ∥ f ar) γ
    where
     ar : ∥ S ∥ f → ∣ A ∣
     ar = λ x → Inv ∣ h ∣ (b x) (b∈Imh x)

     ζ : (λ x → ∣ h ∣ (ar x)) ≡ (λ x → b x)
     ζ = fe (λ x → InvIsInv ∣ h ∣ (b x) (b∈Imh x) )

     γ : ∥ B ∥ f (λ x → b x)
          ≡ ∣ h ∣ (∥ A ∥ f (λ x → Inv ∣ h ∣ (b x) (b∈Imh x)))
     γ =   ∥ B ∥ f (λ x → b x)      ≡⟨ ap ( ∥ B ∥ f ) ζ ⁻¹ ⟩
           ( ∥ B ∥ f ) ( ∣ h ∣ ∘ ar ) ≡⟨ intensionality ξ ar ⟩
            ∣ h ∣ ( ∥ A ∥ f ar )      ∎
      where
       τ : (λ f ar → (∥ B ∥ f)(∣ h ∣ ∘ ar))
            ≡ (λ f ar → ∣ h ∣ (∥ A ∥ f ar ))
       τ = (∥ h ∥)⁻¹
       ξ : (λ (ar : ∥ S ∥ f → ∣ A ∣) → (∥ B ∥ f)(∣ h ∣ ∘ ar))
            ≡ (λ (ar : ∥ S ∥ f → ∣ A ∣) → ∣ h ∣ (∥ A ∥ f ar))
       ξ = dep-intensionality τ f

   finv' : {X : 𝓤 ̇ } (b : X → ∣ HOM-image-alg ∣) (x : X) → ∣ A ∣
   finv' = λ b x → Inv ∣ h ∣ ∣ b x ∣ ∥ b x ∥


-----------------------------------------------------------

Alternative terms
------------------------



Intensional proofs
~~~~~~~~~~~~~~~~~~~

Here we use ``HOM`` instead of ``hom``. N.B. using this "intensional" definition, we shouldn't need function extensionality to prove uniqueness of the homomorphic extension.

::

  module _ {A : Algebra 𝓤 S} {X : 𝓧 ̇ } where

   --1.a. Every map (X → A) lifts.
   free-lift : (h : X → ∣ A ∣)  →  ∣ 𝑻(X) ∣ → ∣ A ∣
   free-lift h (generator x) = h x
   free-lift h (node f args) = ∥ A ∥ f λ i → free-lift h (args i)

   --1.b. that free-lift is (intensionally) a hom.
   lift-HOM : (h : X → ∣ A ∣) →  HOM (𝑻(X)) A
   lift-HOM  h = free-lift h , refl _

   --2. The lift to  (free → A)  is (intensionally) unique.

   free-intensionally-unique : funext 𝓥 𝓤
    →             (g h : HOM (𝑻(X)) A)
    →             (∣ g ∣ ∘ generator) ≡ (∣ h ∣ ∘ generator)
    →             (t : Term)
                 --------------------------------
    →              ∣ g ∣ t ≡ ∣ h ∣ t

   free-intensionally-unique fe g h p (generator x) =
    intensionality p x

   free-intensionally-unique fe g h p (node f args) =
    ∣ g ∣ (node f args)   ≡⟨ ap (λ - → - f args) ∥ g ∥ ⟩
    ∥ A ∥ f(∣ g ∣ ∘ args) ≡⟨ ap (∥ A ∥ _) γ ⟩
    ∥ A ∥ f(∣ h ∣ ∘ args) ≡⟨ (ap (λ - → - f args) ∥ h ∥ ) ⁻¹ ⟩
    ∣ h ∣ (node f args)  ∎
     where
      γ = fe λ i → free-intensionally-unique fe g h p (args i)


Compatibility of homs and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section we present the formal proof of the fact that homomorphisms commute with terms.  More precisely, if A and B are S-algebras, h : A → B a homomorphism, and t a term in the language of S, then for all a : X → ∣ A ∣ we have :math:`h (t^A a) = t^B (h ∘ a)`.

::

  -- Proof of 1. (homomorphisms commute with terms).
  comm-hom-term-intens : global-dfunext
   →              {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
                  (h : HOM A B) (t : Term{X = X})
                 ---------------------------------------------
   →              ∣ h ∣ ∘ (t ̇ A) ≡ (t ̇ B) ∘ (λ a → ∣ h ∣ ∘ a )

  comm-hom-term-intens gfe A B h (generator x) = refl _

  comm-hom-term-intens gfe {X = X}A B h (node f args) = γ
   where
    γ : ∣ h ∣ ∘ (λ a → (f ̂ A) (λ i → (args i ̇ A) a))
        ≡ (λ a → (f ̂ B)(λ i → (args i ̇ B) a)) ∘ _∘_ ∣ h ∣
    γ = ∣ h ∣ ∘ (λ a → (f ̂ A) (λ i → (args i ̇ A) a))
          ≡⟨ ap (λ - → (λ a → - f (λ i → (args i ̇ A) a))) ∥ h ∥ ⟩
        (λ a → (f ̂ B)(∣ h ∣ ∘ (λ i →  (args i ̇ A) a)))
          ≡⟨ refl _ ⟩
        (λ a → (f ̂ B)(λ i → ∣ h ∣ ((args i ̇ A) a)))
          ≡⟨ ap (λ - → (λ a → (f ̂ B)(- a))) ih ⟩
      (λ a → (f ̂ B)(λ i → (args i ̇ B) a)) ∘ _∘_ ∣ h ∣
          ∎
      where
       IH : (a : X → ∣ A ∣)(i : ∥ S ∥ f)
        →   (∣ h ∣ ∘ (args i ̇ A)) a ≡ ((args i ̇ B) ∘ _∘_ ∣ h ∣) a
       IH a i = intensionality (comm-hom-term-intens gfe A B h (args i)) a

       ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ A) a)))
             ≡ (λ a → (λ i → ((args i ̇ B) ∘ _∘_ ∣ h ∣) a))
       ih = gfe λ a → gfe λ i → IH a i


Compatibility of congruences and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we present an Agda proof of the fact that terms respect congruences. More precisely, we show that for every term t, every θ ∈ Con(A), and all tuples a, b : 𝑋 → A, we have :math:`(∀ i, a(i) \mathrel θ b(i)) → (t^A a) \mathrel θ (t^A b)`.

::

  compatible-term-intens : {X : 𝓧 ̇}(A : Algebra 𝓤 S)
                    ( t : Term{X = X} ) (θ : Con A)
                   ---------------------------------
   →                 compatible-fun (t ̇ A) ∣ θ ∣

  compatible-term-intens A (generator x) θ p = p x
  compatible-term-intens A (node f args) θ p =
   pr₂( ∥ θ ∥ ) f λ{x → (compatible-term-intens A (args x) θ) p}

-------------------------

.. include:: hyperlink_references.rst

