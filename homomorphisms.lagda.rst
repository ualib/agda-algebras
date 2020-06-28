.. File: homomorphisms.lagda.rst
.. Author: William DeMeo and Siva Somayyajula
.. Date: 20 Feb 2020
.. Updated: 27 Jun 2020

.. _homomorphisms in agda:

========================
Homomorphisms in Agda
========================

Preliminaries
-------------

As usual, we start with the imports we will need below.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude
   open import basic using (Signature; Algebra)
   open import relations using (ker; ker-pred; Rel; 𝟎; con; _//_)

.. _homomorphisms module:

The homomorphisms module
-------------------------

We start the ``homomorphisms`` module with a fixed signature ``S``.

::

   module homomorphisms {S : Signature 𝓞 𝓥} where


Intensionally homomorphic
-----------------------------

There are two levels of intesionality.

Partial intensionality
~~~~~~~~~~~~~~~~~~~~~~

Here we assume intensionality with respect to 𝒂, but extensional with respect to 𝓸.

::

   --intensional preservation of operations
   op_interpreted-in_and_commutes-intensionally-with :
    (𝓸 : ∣ S ∣ ) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) (f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with f =
    (λ 𝒂 → f (∥ 𝑨 ∥ 𝓸 𝒂) ) ≡ (λ 𝒂 → ∥ 𝑩 ∥ 𝓸 (f ∘ 𝒂) )

The implicit typing judgment here is `𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣`, which represents an (∥ S ∥ 𝓸)-tuple of elements from ∣ 𝑨 ∣.

::

   all-ops-in_and_commute-partially-intensionally-with :
    (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)( f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f =
    ∀  (𝓸 : ∣ S ∣ ) → op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-intensionally-with f

   intensional-hom : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
    →                (∣ 𝑨 ∣ → ∣ 𝑩 ∣) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   intensional-hom 𝑨 𝑩 f = all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f

   Hom : Algebra 𝓦 S → Algebra 𝓤 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   Hom 𝑨 𝑩 = Σ f ꞉ ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , all-ops-in 𝑨 and 𝑩 commute-partially-intensionally-with f


Full intensionality
~~~~~~~~~~~~~~~~~~~~~~

::

   -- intensional with respect to both 𝓸 and 𝒂)
   preserves-ops : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S)
    →              (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   preserves-ops (A , 𝐹ᴬ)(B , 𝐹ᴮ) f =
    (λ (𝓸 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝓸 → A) → f (𝐹ᴬ 𝓸 𝒂))
     ≡ (λ (𝓸 : ∣ S ∣ ) (𝒂 : ∥ S ∥ 𝓸 → A )  → 𝐹ᴮ 𝓸 (f ∘ 𝒂))

   all-ops-in_and_commute-intensionally-with :
    (𝑨 : Algebra 𝓤 S)(𝑩 : Algebra 𝓦 S)( f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   all-ops-in 𝑨 and 𝑩 commute-intensionally-with f = preserves-ops 𝑨 𝑩 f

   --the type of (intensional) homomorphisms
   HOM : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   HOM 𝑨 𝑩 = Σ f ꞉ ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , all-ops-in 𝑨 and 𝑩 commute-intensionally-with f

Extensionally homomorphic
---------------------------

::

   op_interpreted-in_and_commutes-extensionally-with :
    (𝓸 : ∣ S ∣) (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) (f : ∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with f =
    ∀( 𝒂 : ∥ S ∥ 𝓸 → ∣ 𝑨 ∣ )  → f (∥ 𝑨 ∥ 𝓸 𝒂) ≡ ∥ 𝑩 ∥ 𝓸 (f ∘ 𝒂)

   all-ops-in_and_commute-extensionally-with :
    (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → (∣ 𝑨 ∣  → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   all-ops-in 𝑨 and 𝑩 commute-extensionally-with f =
    ∀ (𝓸 : ∣ S ∣ ) → op 𝓸 interpreted-in 𝑨 and 𝑩 commutes-extensionally-with f

   is-homomorphism : (𝑨 : Algebra 𝓤 S) (𝑩 : Algebra 𝓦 S) → ( ∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   is-homomorphism 𝑨 𝑩 f = all-ops-in 𝑨 and 𝑩 commute-extensionally-with f

The type of (extensional) homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::
   hom : Algebra 𝓤 S → Algebra 𝓦 S  → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⊔ 𝓞 ̇
   hom 𝑨 𝑩 = Σ f ꞉ (∣ 𝑨 ∣ → ∣ 𝑩 ∣ ) , is-homomorphism 𝑨 𝑩 f

   𝓲𝓭 :  (A : Algebra 𝓤 S) → hom A A
   𝓲𝓭 _ = (λ x → x) , λ _ _ → refl _ 

Equalizers in Alg
~~~~~~~~~~~~~~~~~~~~~~

(See also 𝑬𝑯 in the ``birkhoff`` module.)

::

   𝓔 : {A : Algebra 𝓤 S} {B : Algebra 𝓦 S} → hom A B → hom A B → 𝓤 ⊔ 𝓦 ̇
   𝓔 (f , _) (g , _) = Σ x ꞉ _ , f x ≡ g x


.. _obs 2 agda:

Compositions of homomorphisms
--------------------------------

::

   -- Obs 2.0. Composing homs gives a hom. (proved in UF-Hom)
   -- See also: Siva's (infix) def of _>>>_ in the Hom.agda file.
   HCompClosed : {𝑨 : Algebra 𝓤 S}
                 {𝑩 : Algebra 𝓦 S}
                 {𝑪 : Algebra 𝓣 S}
    →            hom 𝑨 𝑩   →   hom 𝑩 𝑪
                ------------------------
    →                   hom 𝑨 𝑪

   HCompClosed {𝑨 = A , FA}{𝑩 = B , FB}{ 𝑪 = C , FC }
    (f , fhom) (g , ghom) = g ∘ f , γ
     where
      γ : ( 𝓸 : ∣ S ∣ ) ( 𝒂 : ∥ S ∥ 𝓸  →  A )
       →  ( g ∘ f ) ( FA 𝓸 𝒂 ) ≡ FC 𝓸 ( g ∘ f ∘ 𝒂 )

      γ 𝓸 𝒂 = (g ∘ f) (FA 𝓸 𝒂)     ≡⟨ ap g ( fhom 𝓸 𝒂 ) ⟩
                     g (FB 𝓸 (f ∘ 𝒂))     ≡⟨ ghom 𝓸 ( f ∘ 𝒂 ) ⟩
                     FC 𝓸 (g ∘ f ∘ 𝒂)     ∎

   -- Siva's alternative notation for hom composition
   module _ {A : Algebra 𝓤 S}
            {B : Algebra 𝓦 S}
            {C : Algebra 𝓣 S} where

     _>>>_ : hom A B  → hom B C → hom A C
     (f , fhom) >>> (g , ghom) = g ∘ f , γ
       where
         γ :      (𝓸 : ∣ S ∣ ) → (𝒂 : ∥ S ∥ 𝓸 → ∣ A ∣)
              -------------------------------------------
          →    (g ∘ f) (∥ A ∥ 𝓸 𝒂)  ≡  ∥ C ∥ 𝓸 (g ∘ f ∘ 𝒂)

         γ 𝓸 𝒂 =
          (g ∘ f) (∥ A ∥ 𝓸 𝒂) ≡⟨ ap (λ - → g -) (fhom 𝓸 𝒂) ⟩
          g (∥ B ∥ 𝓸 (f ∘ 𝒂)) ≡⟨ ghom 𝓸 (f ∘ 𝒂) ⟩
          ∥ C ∥ 𝓸 (g ∘ f ∘ 𝒂)  ∎


.. _obs 5 agda:


Factorization of homomorphisms
-----------------------------------

If f : Hom 𝑨 𝑩, g : Hom 𝑨 𝑪, g epic, Ker g ⊆ Ker f, then ∃ h ∈ Hom 𝑪 𝑩, f = h ∘ g.

.. code-block::

        𝑨---f---> 𝑩
         \       ↑
          \     /
        g  \   / ∃h
            ↓ /
             𝑪

::

   homFactor : funext 𝓤 𝓤 → {𝑨 𝑩 𝑪 : Algebra 𝓤 S}
               (f : hom 𝑨 𝑩) (g : hom 𝑨 𝑪)
    →          ker-pred ∣ g ∣ ⊆ ker-pred ∣ f ∣  →   Epic ∣ g ∣
              ---------------------------------------------
    →           Σ h ꞉ ( hom 𝑪 𝑩 ) ,  ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣

   -- To prove: the diagram above commutes; i.e., ∣ f ∣ ≡ ∣ h ∣ ∘ ∣ g ∣.

   homFactor fe {𝑨 = A , FA}{𝑩 = B , FB}{𝑪 = C , FC}
    (f , fhom) (g , ghom) Kg⊆Kf gEpic = (h , hIsHomCB) , f≡h∘g
     where
      gInv : C → A
      gInv = λ c → (EpicInv g gEpic) c

      h : C → B
      h = λ c → f ( gInv c )

      ξ : (x : A) → ker-pred g (x , gInv (g x))
      ξ x =  ( cong-app (EInvIsRInv fe g gEpic) ( g x ) )⁻¹

      f≡h∘g : f ≡ h ∘ g
      f≡h∘g = fe  λ x → Kg⊆Kf (ξ x)

      ζ : (𝓸 : ∣ S ∣)(𝒄 : ∥ S ∥ 𝓸 → C)(x : ∥ S ∥ 𝓸)
       →  𝒄 x ≡ (g ∘ gInv)(𝒄 x)
      ζ 𝓸 𝒄 x = (cong-app (EInvIsRInv fe g gEpic) (𝒄 x))⁻¹

      ι : (𝓸 : ∣ S ∣)(𝒄 : ∥ S ∥ 𝓸 → C)
       →  (λ x → 𝒄 x) ≡ (λ x → g (gInv (𝒄 x)))
      ι 𝓸 𝒄 = ap (λ - → - ∘ 𝒄)(EInvIsRInv fe g gEpic)⁻¹

      useker : (𝓸 : ∣ S ∣)  (𝒄 : ∥ S ∥ 𝓸 → C)
       → f (gInv (g (FA 𝓸 (gInv ∘ 𝒄)))) ≡ f(FA 𝓸 (gInv ∘ 𝒄))
      useker = λ 𝓸 𝒄
       → Kg⊆Kf (cong-app
                (EInvIsRInv fe g gEpic)
                (g(FA 𝓸(gInv ∘ 𝒄)))
               )

      hIsHomCB : (𝓸 : ∣ S ∣)(𝒂 : ∥ S ∥ 𝓸 → C)
       →         h (FC 𝓸 𝒂)  ≡  FB 𝓸 (h ∘ 𝒂)
      hIsHomCB 𝓸 𝒄 =
       f (gInv (FC 𝓸 𝒄))               ≡⟨ i ⟩
       f (gInv (FC 𝓸 (g ∘ (gInv ∘ 𝒄)))) ≡⟨ ii ⟩
       f (gInv (g (FA 𝓸 (gInv ∘ 𝒄))))  ≡⟨ iii ⟩
       f (FA 𝓸 (gInv ∘ 𝒄))             ≡⟨ iv ⟩
       FB 𝓸 (λ x → f (gInv (𝒄 x)))     ∎
       where
        i  = ap (f ∘ gInv) (ap (FC 𝓸) (ι 𝓸 𝒄))
        ii = ap (λ - → f (gInv -)) (ghom 𝓸 (gInv ∘ 𝒄))⁻¹
        iii = useker 𝓸 𝒄
        iv = fhom 𝓸 (gInv ∘ 𝒄)

.. _hom images again:

Homomorphic images again
------------------------

Let  ``𝑯 𝓚``  denote the class of homomorphic images of members of 𝓚.

::

   _is-hom-image-of_ : (𝑩 : Algebra (𝓤 ⁺) S) → (𝑨 : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   𝑩 is-hom-image-of 𝑨 = Σ θ ꞉ (Rel ∣ 𝑨 ∣ _) , con 𝑨 θ  × ((∣ 𝑨 ∣ // θ) ≡ ∣ 𝑩 ∣)

   HomImagesOf : (Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   HomImagesOf 𝑨 = Σ 𝑩 ꞉ (Algebra _ S) , 𝑩 is-hom-image-of 𝑨

   HomImagesOf-pred : (Algebra 𝓤 S) → Pred (Algebra ( 𝓤 ⁺ ) S) (𝓞 ⊔ 𝓥 ⊔ ((𝓤 ⁺) ⁺))
   HomImagesOf-pred 𝑨 = λ 𝑩 → 𝑩 is-hom-image-of 𝑨

   _is-hom-image-of-class_ : {𝓤 : Universe}
    → (Algebra (𝓤 ⁺) S) → (Pred (Algebra 𝓤 S) (𝓤 ⁺)) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   𝑩 is-hom-image-of-class 𝓚 = Σ 𝑨 ꞉ (Algebra _ S) , (𝑨 ∈ 𝓚) × (𝑩 is-hom-image-of 𝑨)

   HomImagesOfClass : {𝓤 : Universe} → Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   HomImagesOfClass 𝓚 = Σ 𝑩 ꞉ (Algebra _ S) , (𝑩 is-hom-image-of-class 𝓚)

   𝑯 : {𝓤 : Universe} → Pred (Algebra 𝓤 S) (𝓤 ⁺) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   𝑯 𝓚 = HomImagesOfClass 𝓚

   -- Here 𝓛𝓚 represents a (Universe-indexed) collection of classes.
   𝑯-closed  :  (𝓛𝓚 : (𝓤 : Universe) → Pred (Algebra 𝓤 S) (𝓤 ⁺))
    →           (𝓤 : Universe) → (Algebra (𝓤 ⁺) S)  →   𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ⁺ ̇
   𝑯-closed 𝓛𝓚 = λ 𝓤 𝑩 → 𝑩 is-hom-image-of-class (𝓛𝓚 𝓤) → 𝑩 ∈ (𝓛𝓚 (𝓤 ⁺))


Isomorphism
---------------

For algebras, isomorphisms are simply homs with 0 kernel.

::

   _≅_ : (A B : Algebra 𝓤 S) → 𝓤 ⊔ 𝓞 ⊔ 𝓥 ̇
   A ≅ B =  Σ f ꞉ (hom A B) , Σ g ꞉ (hom B A) ,
             (∣ f ∣ ∘ ∣ g ∣ ≡ ∣ 𝓲𝓭 B ∣) × (∣ g ∣ ∘ ∣ f ∣ ≡ ∣ 𝓲𝓭 A ∣)

   is-algebra-iso : {A B : Algebra 𝓤 S} (f : hom A B) → 𝓤 ⁺ ̇
   is-algebra-iso {𝓤}{A} f =  ker ∣ f ∣ ≡ 𝟎 {𝓤}{∣ A ∣}

   AlgebraIsos : (A B : Algebra 𝓤 S) → 𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇
   AlgebraIsos {𝓤} A B = Σ f ꞉ (hom A B) , is-algebra-iso {𝓤} {A} {B} f

   _≈_ : Rel (Algebra 𝓤 S) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
   A ≈ B = is-singleton (AlgebraIsos A B)



