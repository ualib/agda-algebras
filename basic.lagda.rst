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

All but the most trivial Agda programs typically begin by importing from existing libraries (e.g., the `Agda Standard Library`_) and setting some options that effect how Agda behaves. In particular, logical axioms and deduction rules can be specified according to what one wishes to assume. 

For example, here's the start of the first Agda source file in our library, which we call ``Preliminaries.agda``.

.. code-block:: agda

   {-# OPTIONS --without-K --exact-split #-}

     --`without-K` disables Streicher's K axiom; see "Note on axiom K" 
     --            of the ualib documentation (ualib.org).
     --
     --`exact-split` makes Agda to only accept definitions with the
     --              equality sign "=" that behave like so-called
     --              judgmental or definitional equalities.

   module Preliminaries where

   -- Export common imports
   open import Level public
   open import Data.Product using (∃; _,_) public
     renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)
   open import Relation.Unary using (Pred; _∈_; _⊆_) public
   open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
   open import Function using (_∘_) public

We don't have the space (or patience!) to describe each of the imports appearing in ``Preliminaries.agda``. Some of them will come up for discussion in due course. Until then, we refer the reader to the above mentioned documentation, as well as the brief :ref:`axiomk` in the appendix; the latter explains the ``--without-K`` option.

The remainder of the ``Preliminaries.agda`` file gives 2 alternative notations for the same simple concept.

.. code-block:: agda

   --1--
   _∈∈_ : {i j k : Level} {A : Set i} {B : Set j}
     ->   (A -> B)
     ->   Pred B k
	 ---------------
     ->   Set (i ⊔ k)
   _∈∈_ {A = A} f S = (x : A) -> f x ∈ S

   --2--
   im_⊆_ : {i j k : Level} {A : Set i} {B : Set j}
     ->    (A -> B)
     ->    Pred B k
	 -------------------
     ->    Set (i ⊔ k)
   im_⊆_ {A = A} f S = (x : A) -> f x ∈ S


-----------------------------------

.. _signatures operations and algebras:

Signatures, Operations, and Algebras
------------------------------------

We may wish to encode arity as an arbitrary type (which Agda denotes ``Set``).

The contents of the  agda-ualib_ file ``Basic.agda`` are as follows:

.. code-block:: agda

   open import Preliminaries
     using (Level; lzero; lsuc;_⊔_; ∃; _,_)

   module Basic where

   -- Operations and projections
   module _ {i j} where
     Op : Set i → Set j → Set (i ⊔ j)
     Op I A = (I → A) → A

     π : {I : Set i} {A : Set j} → I → Op I A
     π i x = x i

   -- i is the universe in which the carrier lives
   -- j is the universe in which the arities live
   Signature : (i j : Level) → Set (lsuc (i ⊔ j))
   Signature i j = ∃ λ (F : Set i) → F → Set j

   -- k is the universe in which the operational type lives
   Algebra : {i j : Level}
	     (k : Level)  ->  Signature i j
	     -------------------------------
     ->      Set (i ⊔ j ⊔ lsuc k)
   Algebra k (𝐹 , ρ) =
     ∃ λ (A : Set k) -> (𝓸 : 𝐹) -> Op (ρ 𝓸) A

.. _signatures in agda:

Signatures in Agda
~~~~~~~~~~~~~~~~~~~~~

   
Notice that, when importing ``Data.Product``, we renamed ``proj₁`` to ``∣_∣`` and ``proj₂`` to ``⟦_⟧``.  Consequently, if e.g. ``S : Signature i j``, then

  ``∣ S ∣`` = the set of operation symbols (which we sometimes call ``𝑭``), and

  ``⟦ S ⟧`` = the arity function (which we sometimes call ``ρ``).

If  ``𝓸 : ∣ S ∣``  is an operation symbol of the signature ``S``, then ``⟦ S ⟧ 𝓸`` denotes the arity of ``𝓸``.

.. For example, the signature of a monoid could be implemented like so.

.. .. code-block:: agda

   ..
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


.. _operations in agda:

Operations in Agda
~~~~~~~~~~~~~~~~~~~~~

As seen above, we represent the notions **operation** and **projection** in Agda as follows:

.. code-block:: agda

   -- Operations and projections
   module _ {i j} where
     Op : Set i → Set j → Set (i ⊔ j)
     Op I A = (I → A) → A

     π : {I : Set i} {A : Set j} → I → Op I A
     π i x = x i

The last two lines above codify the ``i``-th ``I``-ary projection operation on ``A``.

.. _algebras in agda:

Algebras in Agda
~~~~~~~~~~~~~~~~~~

An algebraic structure is represented in our library using the following type:

.. code-block:: agda

   -- k is the universe in which the operational type lives
   Algebra : {i j : Level}
	     (k : Level)  ->  Signature i j
	     -------------------------------
     ->      Set (i ⊔ j ⊔ lsuc k)
   Algebra k (𝐹 , ρ) =
     ∃ λ (A : Set k) -> (𝓸 : 𝐹) -> Op (ρ 𝓸) A

We will have much to say about this type later.  For now, we continue setting down our Agda syntax for the basic objects of universal algebra.

-----------------------------------

.. _homomorphisms in agda:

Homomorphisms in Agda
----------------------

The file called ``Hom.agda`` in agda-ualib_ implements the notions **homomorphism** and **equalizer**, as follows:

.. code-block:: agda

   open import Preliminaries
     using (Level; ∃; _,_; ∣_∣; _≡_; refl; _∘_; Pred)
   open import Basic

   module Hom where

   private
     variable
       i j k : Level
       S : Signature i j

   --The category of algebras Alg with morphisms as Homs

   Hom : Algebra k S -> Algebra k S -> Set _
   Hom {S = 𝑭 , ρ} (A , 𝑨) (B , 𝑩) =
       ∃ λ (f : A -> B) -> (𝓸 : 𝑭) (𝒂 : ρ 𝓸 -> A)
	-----------------------------------------
	 ->    f (𝑨 𝓸 𝒂) ≡ 𝑩 𝓸 (f ∘ 𝒂)

   id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
   id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

   private
     variable
       𝑨 𝑩 : Algebra k S

   _>>>_ : {𝑪 : Algebra k S}

     ->   Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
	 -------------------------
     ->         Hom 𝑨 𝑪

   _>>>_ {S = 𝑭 , ρ} {𝑨 = (A , 𝑭ᴬ)} {𝑪 = (C , 𝑭ᶜ)}
	 (f , α) (g , β) = g ∘ f , γ
	   where
	     γ :    (𝓸 : 𝑭) (𝒂 : ρ 𝓸 -> A)
		  ---------------------------------------
	       ->   (g ∘ f) (𝑭ᴬ 𝓸 𝒂) ≡ 𝑭ᶜ 𝓸 (g ∘ f ∘ 𝒂)
	     γ 𝓸 𝒂 rewrite α 𝓸 𝒂 = β 𝓸 (f ∘ 𝒂)

   -- Equalizers in Alg
   _~_ : Hom 𝑨 𝑩 → Hom 𝑨 𝑩 → Pred ∣ 𝑨 ∣ _
   _~_ (f , _) (g , _) x = f x ≡ g x

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



    
