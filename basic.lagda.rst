.. file: basic.lagda.rst
.. Author: William DeMeo  <williamdemeo@gmail.com>
.. Date: 24 Dec 2019
.. Updated: 29 Jan 2020
.. Note: This was used for the second part of my talk at JMM Special Session.
.. Copyright (c) 2019 William DeMeo

.. _datatypes for algebras:

Datatypes for Algebras
========================

.. _preliminaries:

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

    module basic where

    open import Level
    open import preliminaries
    open import Relation.Unary
    import Relation.Binary as B
    open import Relation.Binary.Core
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl)
    open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
    open import Function using (_∘_)
    open import Function.Equality hiding (_∘_)
    open import Agda.Builtin.Nat public
      renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )
    open import Data.Fin public hiding ( _+_; _<_ )
      renaming ( suc to fsucc; zero to fzero )

We don't have the space (or patience!) to describe each of the above directives. Instead, we refer the reader to the above mentioned documentation (as well as the brief :ref:`axiomk` below, explaining the ``--without-K`` option).

-----------------------------------

.. _signatures in agda:

Signatures in Agda
--------------------

We may wish to encode arity as an arbitrary type (which Agda denotes ``Set``).

.. code-block:: agda

   --------------------------------
   -- A data type for SIGNATURES
   --------------------------------

   record signature : Set₁ where 
     field
       _Ω : Set       -- The "überuniverse" (all universes are subsets of Ω)
       _𝓕 : Set      -- operation symbols.
       _ρ : _𝓕 -> ℕ -- Each operation symbol has an arity.
                      
       -- (for now, use natural number arities, but this isn't essential)

If ``S : signature``, then ``S Ω`` denotes the **überuniverse** of ``S``---the set of which all carriers are subsets--- and ``S 𝓕`` denotes the operation symbols of ``S``.

If  ``𝓸 : S 𝓕``  is an operation symbol of the signature ``S``, then ``S ρ 𝓸`` denotes the arity of ``𝓸``.

For example, the signature of a monoid could be implemented like so.

.. code-block:: agda

   data monoid-op : Set where
     e : monoid-op
     · : monoid-op

   monoid-sig : signature 
   monoid-sig =
     record
       { _Ω = ℕ
       ; _𝓕 = monoid-op
       ; _ρ = λ {e -> 0; · -> 2}
       }


-----------------------------------

.. _operations in agda:

Operations in Agda
--------------------


.. code-block:: agda

   data operation (γ α : Set) : Set where

   o : ((γ -> α) -> α) -> operation γ α

Here, ``γ`` is an "arity type" and ``α`` is a "universe type".

**Example**. the ``i``-th ``γ``-ary projection operation on ``α`` could be implemented like this:

.. code-block:: agda

   π : ∀ {γ α : Set} -> (i : γ) -> operation γ α

   π i =  o λ x -> x i


-----------------------------------


.. _algebras in agda:

Algebras in Agda
--------------------

We have defined three alternative different datatypes for representing algebraic structures.

The first is the simplest, but also the least flexible.

#. **Algebra with carrier of type** ``Set``.

   .. code-block:: agda

      open signature

      record algebra (S : signature) : Set₁ where

        field 
          ⟦_⟧ᵤ : Set
          _⟦_⟧ : (𝓸 : S 𝓕) -> (ℕ -> ⟦_⟧ᵤ) -> ⟦_⟧ᵤ

   If ``(A : algebra S)`` is an algebra of ``signature S``, then ``⟦ A ⟧ᵤ`` denotes the **universe** (or "carrier") of ``A``.

   If ``(𝓸 : S 𝓕)`` is an operation symbol of ``S``, then ``A ⟦ 𝓸 ⟧``  denotes the **interpretation** of ``𝓸`` in ``A``.


#. **Algebra with carrier of type** ``Pred (S Ω) zero`` (a predicate on ``S Ω``).

   When considering substructures, it helps to view all carriers of algebras as subuniverses of some über universe, or "überverse" ``S Ω``.  This is the motivation for our second datatype for algebras, where the universe of an algebra is a predicate of the überverse ``S Ω``.

   .. code-block:: agda

      open signature

      record algebraP (S : signature) : Set₁ where

      field
        ⟦_⟧ₚ : Pred (S Ω) zero
        _⟦_⟧ₒ : (𝓸 : S 𝓕) -> (ℕ -> (S Ω)) -> (S Ω)
        cl : ∀ (𝓸 : S 𝓕) (args : ℕ -> (S Ω))     
             -> (∀(i : ℕ) -> (args i) ∈ ⟦_⟧ₚ)
            ------------------------------------------------
             -> _⟦_⟧ₒ 𝓸 args ∈ ⟦_⟧ₚ

   Note that, because the type signature of ``_⟦_⟧ₒ`` is not as precise as that of ``_⟦_⟧``, we must add a condition ``cl`` which asserts that the carrier (predicate) is closed under all operations.

#. **Algebra with carrier of type** ``Setoid``.

   Finally, when working with quotients, it may help to have a definition of an algebra whose carrier is a ``Setoid`` (a set equipped with a special notion of equivalence of elements of the set.

   .. code-block:: agda

      open signature
      open B.Setoid

      record Algebra (S : signature) : Set₁ where

        field
          ⟦_⟧ᵣ : B.Setoid zero zero
          _⟦_⟧ : (𝓸 : S 𝓕) -> (ℕ -> Carrier ⟦_⟧ᵣ) ->  Carrier ⟦_⟧ᵣ

-----------------------------------

.. _homomorphisms in agda:

Homomorphisms in Agda
---------------------------

We begin this section with the definition of homomorphisms on the first algebra datatype above.  Thereafter, we will define analogous notions for the other algebra datatypes.

#. **Homomorphisms for algebras with carriers of type** ``Set``.

   .. code-block:: agda

      open algebra

      record hom {S : signature}
        (A : algebra S) (B : algebra S) : Set where

        field

          -- The map:
          ⟦_⟧ₕ : ⟦ A ⟧ᵤ -> ⟦ B ⟧ᵤ 

          -- The property the map must have to be a hom:
          homo : ∀ {𝓸 : S 𝓕} (args : ℕ -> ⟦ A ⟧ᵤ)
                 ->  ⟦_⟧ₕ ((A ⟦ 𝓸 ⟧) args) ≡ (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args)

#. **Homomorphisms algebras with carriers of type** ``Pred (S Ω) zero``.

   .. code-block:: agda

      open algebraP

      record homP {S : signature}
	(A : algebraP S) (B : algebraP S) : Set where

	field

	  -- The map:
	  hmap : S Ω -> S Ω  -- <-- type is not very precise :'(

	  -- The property the map must have to be a hom:
	  homoP : ∀ {𝓸 : S 𝓕} (args : ℕ -> (S Ω))
		 ->  hmap ((A ⟦ 𝓸 ⟧ₒ) args) ≡ (B ⟦ 𝓸 ⟧ₒ) (hmap ∘ args)


#. **Homomorphisms for algebra with carriers of type** ``Setoid``.

   .. code-block:: agda

      open Algebra

      record Hom {S : signature}
	(A : Algebra S) (B : Algebra S) : Set where

	field

	  -- The map:
	  ⟦_⟧ₕ : Carrier ⟦ A ⟧ᵣ -> Carrier ⟦ B ⟧ᵣ 

	  -- The property the map must have to be a hom:
	  Homo : ∀ {𝓸 : S 𝓕} (args : ℕ -> Carrier ⟦ A ⟧ᵣ)
	    ->   (_≈_ ⟦ B ⟧ᵣ)  ⟦ (A ⟦ 𝓸 ⟧) args ⟧ₕ  ( (B ⟦ 𝓸 ⟧) (⟦_⟧ₕ ∘ args) )


-----------------------------------------------

.. _isomorphisms in agda:

Isomorphisms in Agda
-------------------------

We define a type for **isomorphism** for each of the three flavors of algebra datatype, as follows.

#. **Isomorphisms for algebras with carriers of type** ``Set``.

   .. code-block:: agda

      open hom

      _≅ᵤ_ :  {S : signature}
	     (A : algebra S) -> (B : algebra S) -> Set _

      A ≅ᵤ B = (∃ f : hom A B)
	->    (∃ g : hom B A)
	->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity _ ) -- ⟦ A ⟧ᵤ
	    ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity _ ) -- ⟦ B ⟧ᵤ 


#. **Isomorphisms for algebras with carriers of type** ``Pred (S Ω) zero``.

   .. code-block:: agda

      open homP

      _≅ₚ_ :  {S : signature}
	     (A : algebraP S) -> (B : algebraP S) -> Set _

      A ≅ₚ B = (∃ f : homP A B)
	->    (∃ g : homP B A)
	->    ( (hmap g) ∘ (hmap f) ≡ identity _ )
	    ∧ ( (hmap f) ∘ (hmap g) ≡ identity _ )

#. **Isomorphisms for algebras with carriers of type** ``Setoid``.

   .. code-block:: agda

      open Hom

      _≅ₛ_ : {S : signature}
	    (A : Algebra S) -> (B : Algebra S) -> Set _

      A ≅ₛ B = (∃ f : Hom A B)
	->    (∃ g : Hom B A)
	->    ( (⟦ g ⟧ₕ ∘ ⟦ f ⟧ₕ) ≡ identity _ ) -- (Carrier ⟦ A ⟧ᵣ) )
	    ∧ ( (⟦ f ⟧ₕ ∘ ⟦ g ⟧ₕ) ≡ identity _ ) -- (Carrier ⟦ B ⟧ᵣ)  )


.. _congruence relations in agda:

Congruence relations in Agda
---------------------------------

Next we wish to define a type for congruence relations. For this we need functions that test whether a given operation or term is **compatible** with a given relation. 

Again, we develop the notions for each of our algebra datatypes.

#. **Congruences for algebras with carriers of type** ``Set``.

   .. code-block:: agda

      lift-rel : {ℓ : Level} {Idx : Set} {X : Set}
	->         Rel X ℓ
		-----------------
	->       Rel (Idx -> X) ℓ
      lift-rel R = λ args₁ args₂ -> ∀ i -> R (args₁ i) (args₂ i)

      compatible-fun : ∀{α γ : Set}
	->   ((γ -> α) -> α)  ->  (Rel α zero)  ->  Set
      compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

      -- relation compatible with an operation
      compatible : ∀ {S : signature}
	->  (A : algebra S)  ->   S 𝓕  
	->   Rel ⟦ A ⟧ᵤ zero  ->  Set _
      compatible A 𝓸 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧) ]⇒ 𝓻

      -- relation compatible with all operations of an algebra
      compatible-alg : ∀ {S : signature}
	->  (A : algebra S) -> Rel ⟦ A ⟧ᵤ zero -> Set _
      compatible-alg {S} A 𝓻 = ∀ 𝓸 -> compatible A 𝓸 𝓻

      -- Congruence relations
      record con {S : signature} (A : algebra S) : Set₁ where
        field
	  ⟦_⟧ᵣ : Rel ⟦ A ⟧ᵤ zero
	  equiv : IsEquivalence ⟦_⟧ᵣ
	  compat : compatible-alg A ⟦_⟧ᵣ

#. **Congruences for algebras with carriers of type** ``Pred (S Ω) zero``.

   .. code-block:: agda

      compatibleP : ∀ {S : signature}
	->  (A : algebraP S)  ->   S 𝓕  
	->   Rel (S Ω) zero  ->  Set _
      compatibleP A 𝓸 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧ₒ) ]⇒ 𝓻

      compatible-algP : ∀ {S : signature}
	->  (A : algebraP S) -> Rel (S Ω) zero -> Set _
      compatible-algP {S} A 𝓻 = ∀ 𝓸 -> compatibleP A 𝓸 𝓻

      record conP {S : signature} (A : algebraP S) : Set₁ where
	field
	  𝓡 : Rel (S Ω) zero     -- type 𝓡 as `\MCR`
	  equivP : IsEquivalence 𝓡
	  compatP : compatible-algP A 𝓡

#. **Congruences for algebras with carriers of type** ``Setoid``.

   .. code-block:: agda

      Compatible : ∀ {S : signature}
	->            S 𝓕  ->  (A : Algebra S)
	->            Rel (Carrier ⟦ A ⟧ᵣ) zero -> Set _
      Compatible 𝓸 A 𝓻 = (lift-rel 𝓻) =[ (A ⟦ 𝓸 ⟧) ]⇒ 𝓻

      Compatible-Alg : ∀ {S : signature}
	-> (A : Algebra S) -> Rel (Carrier ⟦ A ⟧ᵣ) zero -> Set _
      Compatible-Alg {S} A 𝓻 = ∀{𝓸 : S 𝓕} -> Compatible 𝓸 A 𝓻


      record Con {S : signature} (A : Algebra S) : Set₁ where
	field
	  ⟦_⟧ᵣ : Rel (Carrier ⟦ A ⟧ᵣ) zero
	  equiv : IsEquivalence ⟦_⟧ᵣ
	  compat : Compatible-Alg A ⟦_⟧ᵣ

-------------------------------------------

.. _quotients in agda:

Quotients in Agda
---------------------

   .. code-block:: agda

      open Con


      Quotient : {S : signature} (A : Algebra S) -> (θ : Con A) -> Algebra S

      Quotient A θ =
	record {

	  ⟦_⟧ᵣ = record {
		  Carrier = Carrier ⟦ A ⟧ᵣ ;
		  _≈_ = ⟦ θ ⟧ᵣ;
		  isEquivalence = equiv θ } ;

	  _⟦_⟧ = A ⟦_⟧ }



----------------------------

In the next chapter we turn to the important topic of **terms** (the datatypes for which we have defined in the file ``free.agda``).

-----------------------------------------------


.. include:: hyperlink_references.rst



    
