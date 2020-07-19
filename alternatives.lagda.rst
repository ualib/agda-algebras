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
   open import basic using (Signature; Algebra; Op)
   open import relations using (transitive)
   open import homomorphisms using (HOM; Hom; hom; is-homomorphism)

   open import terms
    using (Term; _̇_; _̂_; generator; node; comm-hom-term; comm-hom-term')

   open import Relation.Unary using (⋂)

   module alternatives {S : Signature 𝓞 𝓥} where

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

-------------------------

.. include:: hyperlink_references.rst

