.. FILE: terms.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 20 Feb 2020
.. UPDATE: 27 Jun 2020

.. _types for terms:

===============
Types for Terms
===============

Preliminaries
-------------

As usual, we start with the imports we will need below.

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   open import prelude
   open import basic using (Signature; Algebra; Π')
   open import homomorphisms using (HOM; Hom; hom)
   open import relations using (Con; compatible-fun)

Terms in Agda
------------------------

We developed the notion of a term in a signature informally in :numref:`terms`.  Here we formalize this concept in an Agda module called ``terms``. We start by defining a datatype called ``Term`` which, not surprisingly, represents the type of terms.  The type ``X :  𝓧 ̇`` represents an arbitrary (infinite) collection of "variables."


::

   module terms {S : Signature 𝓞 𝓥} where

   data Term {X : 𝓧 ̇}  :  𝓞 ⊔ 𝓥 ⊔ 𝓧 ̇  where
     generator : X → Term {X = X}
     node : (f : ∣ S ∣) → (t : ∥ S ∥ f → Term {X = X}) → Term

   open Term

The term algebra
~~~~~~~~~~~~~~~~~~

The term algebra was described informally in :numref:`terms`.  Here is how we implement this important algebra in Agda.

::

   𝔉 : {X : 𝓧 ̇} → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧) S
   𝔉 {X = X} = Term{X = X} , node

.. _obs 9 in agda:

The universal property of 𝔉
~~~~~~~~~~~~~~~~~~~~~~~~~~~

We prove

  #. every map ``h : 𝑋 → ∣ A ∣`` lifts to a homomorphism from 𝔉 to A, and
  #. the induced homomorphism is unique.

::

   module _ {A : Algebra 𝓤 S} {X : 𝓧 ̇ } where

    --1.a. Every map (X → A) lifts.
    free-lift : (h : X → ∣ A ∣)  →   ∣ 𝔉 ∣ → ∣ A ∣
    free-lift h (generator x) = h x
    free-lift h (node f args) = ∥ A ∥ f λ i → free-lift h (args i)

    --I. Extensional proofs (using hom's)
    --1.b.' The lift is (extensionally) a hom
    lift-hom : (h : X → ∣ A ∣) →  hom 𝔉 A
    lift-hom h = free-lift h , λ f a → ap (∥ A ∥ _) (refl _)

    --2.' The lift to (free → A) is (extensionally) unique.
    free-unique : funext 𝓥 𝓤 → (g h : hom (𝔉 {X = X}) A)
     →           (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
     →           (t : Term )
                ---------------------------
     →            ∣ g ∣ t ≡ ∣ h ∣ t

    free-unique fe g h p (generator x) = p x
    free-unique fe g h p (node f args) =
       ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
       ∥ A ∥ f (λ i → ∣ g ∣ (args i))  ≡⟨ ap (∥ A ∥ _) γ ⟩
       ∥ A ∥ f (λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
       ∣ h ∣ (node f args)             ∎
       where γ = fe λ i → free-unique fe g h p (args i)

Intensional proofs
~~~~~~~~~~~~~~~~~~~

Here we use ``HOM`` instead of ``hom``. N.B. using this "intensional" definition, we shouldn't need function extensionality to prove uniqueness of the homomorphic extension.

::

    --1.b. that free-lift is (intensionally) a hom.
    lift-HOM : (h : X → ∣ A ∣) →  HOM 𝔉 A
    lift-HOM  h = free-lift h , refl _

    --2. The lift to  (free → A)  is (intensionally) unique.

    free-intensionally-unique : funext 𝓥 𝓤
     →             (g h : HOM (𝔉{X = X}) A)
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

Interpretations
-------------------

Before proceding, we define some syntactic sugar that allows us to replace ``∥ A ∥ f`` with slightly more standard-looking notation, ``f ̂ A``, where f is an operation symbol of the signature S of A.

::

   _̂_ : (f : ∣ S ∣)
    →   (A : Algebra 𝓤 S)
    →   (∥ S ∥ f  →  ∣ A ∣) → ∣ A ∣

   f ̂ A = λ x → (∥ A ∥ f) x

We can now write ``f ̂ A`` for the interpretation of the basic operation ``f`` in the algebra ``A``. N.B. below, we will write ``t ̇ A`` for the interpretation of a *term* ``t`` in ``A``.

.. todo:: Perhaps we can figure out how to use the same notation for both interpretations of operation symbols and terms.

Interpretation of terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let ``t : Term`` be a term and ``A`` an S-algebra. We define the 𝑛-ary operation ``t ̇ A`` on ``A`` by structural recursion on ``t``.

  #. if ``t = x ∈ X`` (a variable) and ``a : X → ∣ A ∣`` is a tuple of elements of ``∣ A ∣``, then ``(t ̇ A) a = a x``.
  #. if ``t = f args``, where ``f ∈ ∣ S ∣`` is an op symbol and ``args : ∥ S ∥ f → Term`` is an (``∥ S ∥ f``)-tuple of terms and ``a : X → ∣ A ∣`` is a tuple from ``A``, then ``(t ̇ A) a = ((f args) ̇ A) a = (f ̂ A) λ{ i → ((args i) ̇ A) a }``

::

   _̇_ : {X : 𝓧 ̇ } → Term{X = X}
    →   (A : Algebra 𝓤 S) → (X → ∣ A ∣) → ∣ A ∣

   ((generator x)̇ A) a = a x

   ((node f args)̇ A) a = (f ̂ A) λ{x → (args x ̇ A) a}


   interp-prod : funext 𝓥 𝓤
    →            {X : 𝓧 ̇}{I : 𝓤 ̇}(p : Term{X = X})
                 (𝒜 : I → Algebra 𝓤 S)
                 (x : X → ∀ i → ∣ (𝒜 i) ∣)
    →            (p ̇ (Π' 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

   interp-prod fe (generator x₁) 𝒜 x = refl _

   interp-prod fe (node f t) 𝒜 x =
    let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
     ∥ Π' 𝒜 ∥ f (λ x₁ → (t x₁ ̇ Π' 𝒜) x)
         ≡⟨ ap (∥ Π' 𝒜 ∥ f ) (fe IH) ⟩
     ∥ Π' 𝒜 ∥ f (λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
         ≡⟨ refl _ ⟩
     (λ i₁ → ∥ 𝒜 i₁ ∥ f (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
         ∎

   interp-prod2 : global-dfunext
    →             {X : 𝓧 ̇ }{I : 𝓤 ̇ }
                  (p : Term{X = X}) (A : I → Algebra 𝓤 S)
        -----------------------------------------------------------
    → (p ̇ Π' A) ≡ λ(args : X → ∣ Π' A ∣)
                      → (λ i → (p ̇ A i)(λ x → args x i))

   interp-prod2 fe (generator x₁) A = refl _

   interp-prod2 fe {X = X} (node f t) A =
     fe λ (tup : X → ∣ Π' A ∣) →
      let IH = λ x → interp-prod fe (t x) A  in
      let tA = λ z → t z ̇ Π' A in
       (f ̂ Π' A) (λ s → tA s tup)
         ≡⟨ refl _ ⟩
       ∥ Π' A ∥ f (λ s →  tA s tup)
         ≡⟨ ap ( ∥ Π' A ∥ f ) (fe  λ x → IH x tup) ⟩
       ∥ Π' A ∥ f (λ s → (λ j → (t s ̇ A j)(λ l → tup l j)))
         ≡⟨ refl _ ⟩
       (λ i → (f ̂ A i)(λ s → (t s ̇ A i)(λ l → tup l i)))
         ∎

.. _obs 10 in agda:

Compatibility of homs and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section we present the formal proof of the fact that homomorphisms commute with terms.  More precisely, if A and B are S-algebras, h : A → B a homomorphism, and t a term in the language of S, then for all a : X → ∣ A ∣ we have :math:`h (t^A a) = t^B (h ∘ a)`.

::

   -- Proof of 1. (homomorphisms commute with terms).
   comm-hom-term : global-dfunext
    →              {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
                   (h : HOM A B) (t : Term{X = X})
                  ---------------------------------------------
    →              ∣ h ∣ ∘ (t ̇ A) ≡ (t ̇ B) ∘ (λ a → ∣ h ∣ ∘ a )

   comm-hom-term gfe A B h (generator x) = refl _

   comm-hom-term gfe {X = X}A B h (node f args) = γ
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
        IH a i = intensionality (comm-hom-term gfe A B h (args i)) a

        ih : (λ a → (λ i → ∣ h ∣ ((args i ̇ A) a)))
              ≡ (λ a → (λ i → ((args i ̇ B) ∘ _∘_ ∣ h ∣) a))
        ih = gfe λ a → gfe λ i → IH a i


.. _obs 11 in agda:

Compatibility of congruences and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we present an Agda proof of the fact that terms respect congruences. More precisely, we show that for every term t, every θ ∈ Con(A), and all tuples a, b : 𝑋 → A, we have :math:`(∀ i, a(i) \mathrel θ b(i)) → (t^A a) \mathrel θ (t^A b)`.

::

   compatible-term : {X : 𝓧 ̇}(A : Algebra 𝓤 S)
                     ( t : Term{X = X} ) (θ : Con A)
                    ---------------------------------
    →                 compatible-fun (t ̇ A) ∣ θ ∣

   compatible-term A (generator x) θ p = p x
   compatible-term A (node f args) θ p =
    pr₂( ∥ θ ∥ ) f λ{x → (compatible-term A (args x) θ) p}

Extensional versions
~~~~~~~~~~~~~~~~~~~~~~~~~

::

   -- Proof of 1. (homomorphisms commute with terms).
   comm-hom-term' : global-dfunext --  𝓥 𝓤
    →               {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
    →               (h : hom A B) (t : Term{X = X}) (a : X → ∣ A ∣)
                  --------------------------------------------
    →               ∣ h ∣ ((t ̇ A) a) ≡ (t ̇ B) (∣ h ∣ ∘ a)

   comm-hom-term' fe A B h (generator x) a = refl _

   comm-hom-term' fe A B h (node f args) a =
    ∣ h ∣ ((f ̂ A)  (λ i₁ → (args i₁ ̇ A) a))
      ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ A) a ) ⟩
    (f ̂ B) (λ i₁ →  ∣ h ∣ ((args i₁ ̇ A) a))
      ≡⟨ ap (_ ̂ B)(fe (λ i₁ → comm-hom-term' fe A B h (args i₁) a))⟩
    (f ̂ B) (λ r → (args r ̇ B) (∣ h ∣ ∘ a))
      ∎

   -- Proof of 2. (If t : Term, θ : Con A, then a θ b → t(a) θ t(b))
   compatible-term' : {X : 𝓧 ̇}
              (A : Algebra 𝓤 S) (t : Term{X = X}) (θ : Con A)
              --------------------------------------------------
    →                   compatible-fun (t ̇ A) ∣ θ ∣

   compatible-term' A (generator x) θ p = p x

   compatible-term' A (node f args) θ p =
    pr₂( ∥ θ ∥ ) f λ{x → (compatible-term' A (args x) θ) p}

For proof of 3, see `TermImageSub` in Subuniverse.agda.

..    #. For every subset Y of A,  Sg ( Y ) = { t (a₁, ..., aₙ ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.


------------------

.. include:: hyperlink_references.rst

