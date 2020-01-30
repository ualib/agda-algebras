.. file: subuniverses.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 25 Dec 2019
.. Updated: 29 Jan 2020
.. Copyright (c) 2019 William DeMeo

.. _Datatypes for Subalgebras:

Datatypes for Subuniverses and Subalgebras
============================================

(The code described in this chapter resides in ``subuniverse.agda``.)

As usual, we begin by setting some options and importing some modules.

.. code-block:: agda
		
    {-# OPTIONS --without-K --exact-split #-}

    open import Level
    open import basic
    open algebra
    open signature

    module subuniverse {ℓ : Level} {S : signature} where

    open import preliminaries
    open import Data.Empty
    open import Data.Unit.Base using (⊤)
    open import Data.Product
    open import Data.Sum using (_⊎_; [_,_])
    open import Function
    open import Relation.Unary
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-----------------------------------------------

Subuniverses
------------------

To test whether a subset of a universe is a subuniverse, first we have to decide how to model subsets.

One option is to model a subset of ⟦ A ⟧ᵤ as a *predicate* (i.e., *unary relation*) on ⟦ A ⟧ᵤ.

The ``Pred`` type is defined in the Agda standard library, in the file ``Relation/Unary.agda``, as follows:

.. code-block:: agda

    Pred : ∀ {a}
      ->   Set a  ->   (ℓ : Level)
         ---------------------------
      ->     Set (a ⊔ suc ℓ)

    Pred A ℓ = A -> Set ℓ

So if we let ``B : Pred ⟦ A ⟧ᵤ ℓ``, then ``B`` is simply a function of type ``A -> Set ℓ``.

If we consider some element ``x : ⟦ A ⟧ᵤ``, then ``x ∈ B`` iff ``B x`` "holds" (i.e., is inhabited).

Next, we define a function ``OpClosed`` which asserts that a given subset, ``B``, of ``⟦ A ⟧ᵤ`` is closed under the basic operations of ``A``.

.. code-block:: agda

    OpClosed : (A : algebra S) (B : Pred ⟦ A ⟧ᵤ ℓ) -> Set ℓ
    OpClosed A B = ∀{𝓸 : ⟨ S ⟩ₒ}
                   (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ) 
      ->           ( ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ B )
	         ---------------------------------------------
      ->           (A ⟦ 𝓸 ⟧) args ∈ B

In other terms, ``OpClosed A B`` asserts that for every operation symbol ``𝓸`` of ``A``, and for all tuples ``args`` of arguments, if the antecedent ``(args i) ∈ B`` holds for all ``i`` (i.e., all arguments belong to ``B``), then ``(A ⟦ 𝓸 ⟧) args`` also belongs to ``B``.

Finally, we define the ``IsSubuniverse`` type as a record with two fields: (1) a subset and (2) a proof that the subset is closed under the basic operations.

.. code-block:: agda

    record IsSubuniverse {A : algebra S} : Set (suc ℓ) where

      field
	sset : Pred ⟦ A ⟧ᵤ ℓ       -- a subset of the carrier,
	closed : OpClosed A sset  -- closed under the operations of A

To reiterate, we have ``sset : Pred ⟦ A ⟧ᵤ ℓ``, indicating that ``sset`` is a subset of the carrier ``⟦ A ⟧ᵤ``, and ``closed : OpClosed A sset`` indicating that ``sset`` is closed under the operations of ``A``.

-----------------------------------------------

Subalgebras
---------------

Finally, we define a datatype for subalgebras of a given algebra ``A``.  We choose record with three fields:

  #. a subset, ``subuniv``, of ``A``;
  #. operations, which are the same as ``A`` (we could be pedantic and require the operations be restricted to the subset ``subuniv``, but this is unnecessary);
  #. a proof, named ``closed``, that ``subuniv`` is closed under the operations of ``A``.

.. code-block:: agda

    record subalgebra (A : algebra S) : Set (suc ℓ) where

      field

	subuniv : Pred ⟦ A ⟧ᵤ ℓ

	_⟦_⟧ : (𝓸 : ⟨ S ⟩ₒ)
	  ->   (args : Fin (⟨ S ⟩ₐ 𝓸) -> ⟦ A ⟧ᵤ)
          ->   ( ∀(i : Fin (⟨ S ⟩ₐ 𝓸)) -> (args i) ∈ subuniv )
               -----------------------------------------------
          ->   Set ℓ

	closed : OpClosed A subuniv


    open IsSubuniverse

    SubAlgebra : (A : algebra S)
      ->         (B : IsSubuniverse {A})
                -------------------------
      ->         (subalgebra A)

    SubAlgebra A B =
      record
	{
	subuniv = sset B ;
	_⟦_⟧ = λ 𝓸 args p -> (sset B) ((A ⟦ 𝓸 ⟧) args) ;
	closed = closed B
	}


------------------------------------------------------

.. include:: hyperlink_references.rst
