.. FILE: terms.lagda.rst
.. AUTHOR: William DeMeo and Siva Somayyajula
.. DATE: 20 Feb 2020
.. UPDATE: 10 Jul 2020

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
  open import basic using (Signature; Algebra; Π'; _̂_)
  open import homomorphisms using (hom)
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

The term algebra 𝑻(X)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The term algebra was described informally in :numref:`terms`.  We denote this important algebra by 𝑻(X) and we implement it in Agda as follows.

::

  --The term algebra 𝑻(X).
  𝑻 : 𝓧 ̇ → Algebra (𝓞 ⊔ 𝓥 ⊔ 𝓧) S
  𝑻 X = Term{X = X} , node


.. _obs 9 in agda:

The universal property of 𝑻(X)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We prove

  #. every map ``h : 𝑋 → ∣ 𝑨 ∣`` lifts to a homomorphism from 𝑻(X) to A, and
  #. the induced homomorphism is unique.

::

  module _ {𝑨 : Algebra 𝓤 S} {X : 𝓧 ̇ } where

First, every map ``X → ∣ 𝑨 ∣`` lifts to a homomorphism.

::

   free-lift : (h : X → ∣ 𝑨 ∣)  →  ∣ 𝑻 X ∣ → ∣ 𝑨 ∣
   free-lift h (generator x) = h x
   free-lift h (node f args) = ∥ 𝑨 ∥ f λ i → free-lift h (args i)

   lift-hom : (h : X → ∣ 𝑨 ∣) →  hom  (𝑻 X) 𝑨
   lift-hom h = free-lift h , λ f a → ap (∥ 𝑨 ∥ _) (refl _)

Next, the lift to (𝑻 X → A) is unique.

::

   free-unique : funext 𝓥 𝓤 → (g h : hom (𝑻 X) 𝑨)
    →           (∀ x → ∣ g ∣ (generator x) ≡ ∣ h ∣ (generator x))
    →           (t : Term )
               ---------------------------
    →            ∣ g ∣ t ≡ ∣ h ∣ t

   free-unique fe g h p (generator x) = p x
   free-unique fe g h p (node f args) =
    ∣ g ∣ (node f args)            ≡⟨ ∥ g ∥ f args ⟩
    ∥ 𝑨 ∥ f (λ i → ∣ g ∣ (args i))  ≡⟨ ap (∥ 𝑨 ∥ _) γ ⟩
    ∥ 𝑨 ∥ f (λ i → ∣ h ∣ (args i))  ≡⟨ (∥ h ∥ f args)⁻¹ ⟩
    ∣ h ∣ (node f args)             ∎
     where γ = fe λ i → free-unique fe g h p (args i)


Interpretation of terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let ``t : Term`` be a term and ``𝑨`` an S-algebra. We define the 𝑛-ary operation ``t ̇ 𝑨`` on ``𝑨`` by structural recursion on ``t``.

  #. if ``t = x ∈ X`` (a variable) and ``a : X → ∣ 𝑨 ∣`` is a tuple of elements of ``∣ 𝑨 ∣``, then ``(t ̇ 𝑨) a = a x``.
  #. if ``t = f args``, where ``f ∈ ∣ S ∣`` is an op symbol and ``args : ∥ S ∥ f → Term`` is an (``∥ S ∥ f``)-tuple of terms and ``a : X → ∣ 𝑨 ∣`` is a tuple from ``𝑨``, then ``(t ̇ 𝑨) a = ((f args) ̇ 𝑨) a = (f ̂ 𝑨) λ{ i → ((args i) ̇ 𝑨) a }``

::

  _̇_ : {X : 𝓧 ̇ } → Term{X = X}
   →   (𝑨 : Algebra 𝓤 S) → (X → ∣ 𝑨 ∣) → ∣ 𝑨 ∣

  ((generator x)̇ 𝑨) a = a x

  ((node f args)̇ 𝑨) a = (f ̂ 𝑨) λ{x → (args x ̇ 𝑨) a}


  interp-prod : funext 𝓥 𝓤
   →            {X : 𝓧 ̇}{I : 𝓤 ̇}(p : Term{X = X})
                (𝒜 : I → Algebra 𝓤 S)
                (x : X → ∀ i → ∣ (𝒜 i) ∣)
   →            (p ̇ (Π' 𝒜)) x ≡ (λ i → (p ̇ 𝒜 i) (λ j → x j i))

  interp-prod fe (generator x₁) 𝒜 x = refl _

  interp-prod fe (node f t) 𝒜 x =
   let IH = λ x₁ → interp-prod fe (t x₁) 𝒜 x in
    (f ̂ Π' 𝒜)(λ x₁ → (t x₁ ̇ Π' 𝒜) x)
        ≡⟨ ap (f ̂ Π' 𝒜 ) (fe IH) ⟩
    (f ̂ Π' 𝒜 )(λ x₁ → (λ i₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
        ≡⟨ refl _ ⟩
    (λ i₁ → (f ̂ 𝒜 i₁) (λ x₁ → (t x₁ ̇ 𝒜 i₁) (λ j₁ → x j₁ i₁)))
        ∎

  interp-prod2 : global-dfunext
   →             {X : 𝓧 ̇ }{I : 𝓤 ̇ }
                 (p : Term{X = X}) (𝒜 : I → Algebra 𝓤 S)
    -----------------------------------------------------------
   → (p ̇ Π' 𝒜) ≡ λ(args : X → ∣ Π' 𝒜 ∣)
                    → (λ i → (p ̇ 𝒜 i)(λ x → args x i))

  interp-prod2 fe (generator x₁) 𝒜 = refl _

  interp-prod2 fe {X = X} (node f t) 𝒜 =
   fe λ (tup : X → ∣ Π' 𝒜 ∣) →
    let IH = λ x → interp-prod fe (t x) 𝒜  in
    let tA = λ z → t z ̇ Π' 𝒜 in
     (f ̂ Π' 𝒜) (λ s → tA s tup)
        ≡⟨ refl _ ⟩
     (f ̂ Π' 𝒜) (λ s →  tA s tup)
        ≡⟨ ap (f ̂ Π' 𝒜) (fe  λ x → IH x tup) ⟩
     (f ̂ Π' 𝒜) (λ s → (λ j → (t s ̇ 𝒜 j)(λ l → tup l j)))
        ≡⟨ refl _ ⟩
     (λ i → (f ̂ 𝒜 i)(λ s → (t s ̇ 𝒜 i)(λ l → tup l i)))
        ∎

.. _obs 10 in agda:

Compatibility of homs and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In this section we present the formal proof of the fact that homomorphisms commute with terms.  More precisely, if A and B are S-algebras, h : A → B a homomorphism, and t a term in the language of S, then for all a : X → ∣ A ∣ we have :math:`h (t^A a) = t^B (h ∘ a)`.


.. _obs 11 in agda:

Homomorphisms commute with terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

  comm-hom-term : global-dfunext --  𝓥 𝓤
   →               {X : 𝓧 ̇}(A : Algebra 𝓤 S) (B : Algebra 𝓦 S)
   →               (h : hom A B) (t : Term{X = X}) (a : X → ∣ A ∣)
                 --------------------------------------------
   →               ∣ h ∣ ((t ̇ A) a) ≡ (t ̇ B) (∣ h ∣ ∘ a)

  comm-hom-term fe A B h (generator x) a = refl _

  comm-hom-term fe A B h (node f args) a =
   ∣ h ∣ ((f ̂ A)  (λ i₁ → (args i₁ ̇ A) a))
     ≡⟨ ∥ h ∥ f ( λ r → (args r ̇ A) a ) ⟩
   (f ̂ B) (λ i₁ →  ∣ h ∣ ((args i₁ ̇ A) a))
     ≡⟨ ap (_ ̂ B)(fe (λ i₁ → comm-hom-term fe A B h (args i₁) a))⟩
   (f ̂ B) (λ r → (args r ̇ B) (∣ h ∣ ∘ a))
     ∎

Compatibility of congruences and terms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we present an Agda proof of the fact that terms respect congruences. More precisely, we show that for every term t, every θ ∈ Con(A), and all tuples a, b : 𝑋 → A, we have :math:`(∀ i, a(i) \mathrel θ b(i)) → (t^A a) \mathrel θ (t^A b)`.

::

  -- If t : Term, θ : Con A, then a θ b → t(a) θ t(b)
  compatible-term : {X : 𝓧 ̇}
             (A : Algebra 𝓤 S) (t : Term{X = X}) (θ : Con A)
             --------------------------------------------------
   →                   compatible-fun (t ̇ A) ∣ θ ∣

  compatible-term A (generator x) θ p = p x

  compatible-term A (node f args) θ p =
   pr₂( ∥ θ ∥ ) f λ{x → (compatible-term A (args x) θ) p}

For proof of 3, see `TermImageSub` in subuniverses.lagda.

..    #. For every subset Y of A,  Sg ( Y ) = { t (a₁, ..., aₙ ) : t ∈ T(Xₙ), n < ω, aᵢ ∈ Y, i ≤ n}.


------------------

.. include:: hyperlink_references.rst

