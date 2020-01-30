.. file: basic.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 24 Dec 2019
.. Updated: 29 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.
.. Copyright (c) 2019 William DeMeo

.. _Datatypes for Algebras:

Datatypes for Algebras
========================

Preliminaries
-------------------------

All but the most trivial Agda programs typically begin by importing stuff from existing libraries (e.g., the `Agda Standard Library`_) and setting some options that effect how Agda behaves. In particular, one can specify which logical axioms and deduction rules one wishes to assume. 

For example, here's the start of the first Agda source file in our library, which we call ``basic.agda``.

.. code-block:: agda

    {-# OPTIONS --without-K --exact-split #-}

    --without-K disables Streicher's K axiom
    --(see "NOTES on Axiom K" below).

    --exact-split makes Agda to only accept definitions
    --with the equality sign "=" that behave like so-called
    --judgmental or definitional equalities.

    open import Level

    module basic where

    open import Function using (_∘_)
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open Eq.≡-Reasoning
    open import Relation.Unary

    open import Agda.Builtin.Nat public
      renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )

    open import Data.Fin public
      -- (See "NOTE on Fin" section below)
      hiding ( _+_; _<_ )
      renaming ( suc to fsucc; zero to fzero )

We don't have the time (or patience!) to describe each of the above directives. Instead, we refer the reader to the above mentioned documentation (as well as the brief :ref:`axiomk` below, explaining the ``--without-K`` option).

-----------------------------------

Signatures
-------------

We may wish to encode arity as an arbitrary type (which Agda denotes ``Set``).

.. code-block:: agda

   record signature₁ : Set₁ where 
     field
       ⟨_⟩ₒ : Set        -- operation symbols.
       ⟨_⟩ₐ : ⟨_⟩ₒ -> Set -- Each operation symbol has an arity.

If ``S : signature₁`` is a signature, then ``⟨ S ⟩ₒ`` denotes the operation symbols of ``S``.

If  ``𝓸 : ⟨ S ⟩ₒ``  is an operation symbol, then ``⟨ S ⟩ₐ 𝓸`` is the arity of ``𝓸``.

If you don't like denoting operation symbols of ``S`` by ``⟨ S ⟩ₒ``, 

then maybe something like this would do better.

.. code-block:: agda

   record signature₂ : Set₁ where
     field
       𝓕 : Set
       ρ : 𝓕 -> Set

In that case, if ``𝓸 : 𝓕 S`` is an operation symbol, then ``(ρ S) 𝓸`` is the arity of ``𝓸``.

However, it may seem more natural to most algebraists for the arity to be a natural number.

So let us define ``signature`` once and for all as follows:

.. code-block:: agda

    record signature : Set₁ where 
      field
	⟨_⟩ₒ : Set
	⟨_⟩ₐ : ⟨_⟩ₒ -> ℕ


-----------------------------------

Operations
--------------


.. code-block:: agda

   data operation (γ α : Set) : Set where

   o : ((γ -> α) -> α) -> operation γ α

Here, ``γ`` is an "arity type" and ``α`` is a "universe type".

**Example**. the ``i``-th ``γ``-ary projection operation on ``α`` could be implemented like this:

.. code-block:: agda

   π : ∀ {γ α : Set} -> (i : γ) -> operation γ α

   π i =  o λ x -> x i




-----------------------------------

Algebras
--------------


.. code-block:: agda

    open operation
    open signature

    record algebra' (S : signature) : Set₁ where

      field
	carrier : Set
	ops : (𝓸 : ⟨ S ⟩ₒ)                --op symbol
	  ->  (Fin (⟨ S ⟩ₐ 𝓸) -> carrier) --tuple of args
              ---------------------------
	  ->   carrier                     


If  ``(A : algebra S)`` is an algebra of ``signature S``, then ``carrier A`` would denote the **universe** of ``A``.

If   ``(𝓸 : ⟨ S ⟩ₒ)``   is an operation symbol of ``S``, then ``(op A) 𝓸``  would denote the **interpretation** of ``𝓸`` in ``A``.


**Alternatively**...


.. code-block:: agda

    record algebra (S : signature) : Set₁ where

      field
	⟦_⟧ᵤ : Set
	_⟦_⟧ : (𝓸 : ⟨ S ⟩ₒ)
	  ->   (Fin (⟨ S ⟩ₐ 𝓸) -> ⟦_⟧ᵤ)
              --------------------------
	  ->   ⟦_⟧ᵤ

In that case, if   ``(A : algebra S)``   is an algebra in ``signature S``, then ``⟦ A ⟧ᵤ`` denotes the universe of ``A``.

If   ``𝓸 : ⟨ S ⟩ₒ``   is an operation symbol, ``A ⟦ 𝓸 ⟧``   denotes the interpretation of ``𝓸`` in ``A``.

That's a *little* better... but feel free to invent your own syntax!



-----------------------------------

Homomorphisms
----------------

.. code-block:: agda

    open algebra

    record Hom {S : signature}
      (A : algebra S) (B : algebra S) : Set where

      field

	-- The map:
	⟦_⟧ₕ : ⟦ A ⟧ᵤ -> ⟦ B ⟧ᵤ 

	-- The property the map must have to be a hom:
	homo : ∀ {𝓸 : ⟨ S ⟩ₒ}
	       (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ)
            ---------------------------------------------------
          ->   ⟦_⟧ₕ ((A ⟦ 𝓸 ⟧) args) ≡ (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args)

----------------------------

In the next chapter we turn to the important topic of **terms** (the datatypes for which we have defined in the file ``free.agda``).

-----------------------------------------------


.. include:: hyperlink_references.rst
