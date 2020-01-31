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


-------------

(**A.N.** The following theorem and proof are identical to Prop 1.12 of :cite:`Bergman:2012`, modulo notation.)

.. _subintersection:

.. proof:theorem::

   If 𝑨 is an algebra and ℐ is a nonempty collection of subuniverses of 𝑨, then ⋂ ℐ is a subuniverse of 𝑨.

   .. container:: toggle
    
      .. container:: header
  
         **Proof**.

      Call the intersection 𝐵. Certainly 𝐵 ⊆ 𝐴. Let 𝑓 be a basic 𝑛-ary operation of 𝑨, and let 𝑏 ∈ 𝐵ⁿ. Then for every 𝑆 ∈ ℐ,  and each 𝑘, we have 𝑏 𝑘 ∈ 𝑆, so, since 𝑆 is a subuniverse, 𝑎 = 𝑓 𝑏 ∈ 𝑆.  Now 𝑎 ∈ 𝑆 for every 𝑆 ∈ ℐ, so 𝑎 ∈ 𝐵.


      
----------------------------

Subuniverse generation
-----------------------

Let 𝑨 = ⟨ A, ...⟩ be an algebra and X ⊆ A a subset of the universe of 𝑨.  

(**A.N.** The following definition is identical to Def 1.13 of :cite:`Bergman:2012`, mod notation.)

.. _def-B-1-3:

.. proof:definition::

   The subuniverse of 𝑨 generated by 𝑋 is :math:`\mathrm{Sg}^𝑨` (𝑋) = ⋂ { 𝑈 ∈ Sub(𝑨) : 𝑋 ⊆ 𝑈}.

Although :numref:`Theorem %s <subintersection>` ensures that :math:`\mathrm{Sg}^𝑨(X)` exists and contains 𝑋, it does not give a feel for what objects the subuniverse generated by 𝑋 contains. Fortunately, there is a nice "bottom-up" description of :math:`\mathrm{Sg}^𝑨(X)`.

(**A.N.** The next theorem and proof are nearly identical to Thm 1.14 of :cite:`Bergman:2012`, mod notation.)
     
.. proof:theorem::

   Let 𝑨 = ⟨𝐴, 𝐹⟩ be an algebra and 𝑋 ⊆ 𝐴. Define, by recursion on 𝑛, the sets :math:`𝑋_𝑛` by:

     :math:`𝑋₀ = 𝑋`;

     :math:`𝑋_{n+1} = 𝑋_n ∪ \{ f a : f ∈ F, a ∈ X_n^{ρ f} \}`.

   Then :math:`\mathrm{Sg}^𝐴(X) = ⋃_{n ∈ ω} X_n`.

   .. container:: toggle
    
      .. container:: header
  
         **Proof**.

      In what follows, we write Sg(𝑋) in place of :math:`\mathrm{Sg}^𝑨(X)`.

      Let :math:`𝑌 = ⋃_{n ∈ ω} X_n` Clearly :math:`𝑋_𝑛 ⊆ Y ⊆ 𝐴`, for every 𝑛 ∈ ω. In particular 𝑋 = 𝑋₀ ⊆ 𝑌.

      Let us show that 𝑌 is a subuniverse of 𝑨.

      Let 𝑓 be a basic 𝑘-ary operation and 𝑎 ∈ 𝑌ᵏ.

      From the construction of 𝑌, there is an 𝑛 ∈ ω such that 𝑎 𝑖 ∈ 𝑋ₙ, for all 𝑖 < 𝑘.

      From its definition, 𝑓 𝑎 ∈ :math:`𝑋_{n+1}` ⊆ 𝑌, so 𝑌 is a subuniverse of 𝑨 containing 𝑋.

      By :numref:`Definition %s <def-B-1-3>` , Sg(𝑋) ⊆ 𝑌.

      For the opposite inclusion, it is enough to check, by induction on 𝑛, that 𝑋ₙ ⊆ Sg(𝑋).

      Well, 𝑋₀ = 𝑋 ⊆ Sg(𝑋) from its definition. Assume 𝑋ₙ ⊆ Sg(𝑋).

      If 𝑏 ∈ :math:`X_{n+1} - X_n` then 𝑏 = 𝑓 𝑎 for a basic 𝑘-ary operation 𝑓 and 𝑎 ∈ 𝑋ₙᵏ.

      But 𝑎 ∈ (Sg(𝑋))ᵏ and since this latter object is a subuniverse, 𝑏 ∈ Sg(𝑋) as well.

      □


	
------------------------------------------------------

.. include:: hyperlink_references.rst
