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
   open import Level public renaming (suc to lsuc ; zero to lzero)
   open import Data.Empty using (⊥) public
   open import Data.Bool using (Bool) public
   --open import Data.Product using (∃; _,_; _×_; proj₁; proj₂) public
   open import Data.Product using (∃; _,_; _×_) public
     renaming (proj₁ to ∣_∣; proj₂ to ⟦_⟧)

   open import Relation.Unary using (Pred; _∈_; _⊆_; ⋂) public
   open import Relation.Binary public
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; trans; cong; cong-app; sym; subst) public
   open Eq.≡-Reasoning public
   open import Function using (_∘_) public
   open import Agda.Builtin.Nat public
     renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )

We don't have the space (or patience!) to describe each of the imports appearing in ``Preliminaries.agda``. Some of them will come up for discussion in due course. Until then, we refer the reader to the above mentioned documentation, as well as the brief :ref:`axiomk` in the appendix; the latter explains the ``--without-K`` option.

The full ``Preliminaries.agda`` file, which defines other notation and objects we will use throughout the library, appears in the appendix :ref:`preliminaries.agda`. We will describe each of the objects defined therein as they come up in later sections.

-----------------------------------

.. _signatures operations and algebras:

Signatures, Operations, and Algebras
------------------------------------

We may wish to encode arity as an arbitrary type (which Agda denotes ``Set``).

The contents of the  agda-ualib_ file ``Basic.agda`` are as follows:

.. code-block:: agda

   {-# OPTIONS --without-K --exact-split #-}

   open import Preliminaries
     using (Level; lzero; lsuc;_⊔_; ∃; _,_; ⊥; Bool;
	    _×_; ∣_∣; ⟦_⟧; _≡_; _∘_; Pred; _∈_; Lift)

   module Basic where

   -- Operations and projections
   module _ {i j} where
     Op : Set i → Set j → Set (i ⊔ j)
     Op I A = (I → A) → A

     π : {I : Set i} {A : Set j} → I → Op I A
     π i x = x i

   -- i is the universe in which the operation symbols lives
   -- j is the universe in which the arities live
   Signature : (i j : Level) → Set _
   Signature i j = ∃ λ (F : Set i) → F → Set j

   private
     variable
       i j : Level

   -- k is the universe in which the operational type lives
   Algebra : (k : Level)  ->  Signature i j
	     -------------------------------
     ->      Set _
   Algebra k (𝐹 , ρ) =
     ∃ λ (A : Set k) -> (𝓸 : 𝐹) -> Op (ρ 𝓸) A

   private
     variable
       k l m : Level
       S : Signature i j

   -- Indexed product of algebras is an algebra
   -- The trick is to view the Pi-type as a dependent product i.e.
   -- A i1 × A i2 × A i3 × ... = (i : I) → A i
   Π : {I : Set m} → (I → Algebra k S) → Algebra (k ⊔ m) S
   Π {I = I} A = ((i : I) → ∣ A i ∣) , λ 𝓸 x i → ⟦ A i ⟧ 𝓸 λ j → x j i

   -- Keep I at the same universe as A so that both A and Π A can
   -- be classified by PClo
   data PClo {i j k l} {S : Signature i j} (K : Pred (Algebra k S) l) :
     Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l)) where
       pbase : {A : Algebra _ S} -> A ∈ K -> A ∈ PClo K
       prod : {I : Set k} {A : I -> Algebra _ S}
	 ->   (∀ i -> A i ∈ PClo K) -> Π A ∈ PClo K

   -- Subalgebras
   module _ {i j k : Level} {S : Signature i j} where
     -- To keep A at same universe level as ∃ P , B, force P to live
     -- in the same universe. We need to do this so that both A and
     -- ∃ P , B can be classified by the same predicate SClo.
     data _is-supalgebra-of_ (A : Algebra k S) :
       Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k))
       where
       mem : {P : Pred ∣ A ∣ k} {B : (o : ∣ S ∣) -> Op (⟦ S ⟧ o) (∃ P)}
	 ->  ((o : ∣ S ∣) -> (x : ⟦ S ⟧ o -> ∃ P)
	   -> ∣ B o x ∣ ≡ ⟦ A ⟧ o (λ i → ∣ x i ∣))
	 ->  A is-supalgebra-of (∃ P , B)

     _is-subalgebra-of_ : Algebra _ S → Algebra _ S → Set _
     B is-subalgebra-of A = A is-supalgebra-of B

     data SClo (K : Pred (Algebra k S) l) :
       Pred (Algebra k S) (lsuc (i ⊔ j ⊔ k ⊔ l))
       where
       sbase : {A : Algebra _ S} -> A ∈ K -> A ∈ SClo K
       sub : ∀ {A : Algebra _ S} {B : Algebra _ S}
	 ->  A ∈ SClo K
	 ->  B is-subalgebra-of A
	 ->  B ∈ SClo K

   --Example: monoid
   --  A monoid signature has two operation symbols, say, `e`
   --  and `·`, of arities 0 and 2, of types `(Empty -> A) -> A`
   --  and `(Bool -> A) -> A`, resp. The types indicate that `e`
   --  is nullary (i.e., takes no args, equivalently, takes args
   --  of type `Empty -> A`), while `·` is binary, as indicated
   --  by argument type `Bool -> A`.

   data monoid-op : Set where
     e : monoid-op
     · : monoid-op

   monoid-sig : Signature _ _
   monoid-sig = monoid-op , λ { e → ⊥; · → Bool }

.. _signatures in agda:

Signatures in Agda
~~~~~~~~~~~~~~~~~~~~~

Notice that, when importing ``Data.Product``, we renamed ``proj₁`` to ``∣_∣`` and ``proj₂`` to ``⟦_⟧``.  Consequently, if e.g. ``S : Signature i j``, then

  ``∣ S ∣`` = the set of operation symbols (which we sometimes call ``𝑭``), and

  ``⟦ S ⟧`` = the arity function (which we sometimes call ``ρ``).

If  ``𝓸 : ∣ S ∣``  is an operation symbol of the signature ``S``, then ``⟦ S ⟧ 𝓸`` denotes the arity of ``𝓸``.


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

The file called ``Hom.agda`` in agda-ualib_ implements the notions **homomorphism** and **equalizer**. Here are the contents of ``Hom.agda``.

.. code-block:: agda

   {-# OPTIONS --without-K --exact-split #-}

   open import Preliminaries
   open import Basic

   module Hom where

   private
     variable
       i j k l m : Level
       S : Signature i j
       𝑨 : Algebra k S
       𝑩 : Algebra l S
       𝑪 : Algebra m S

   --The category of algebras Alg with morphisms as Homs
   Hom : Algebra k S -> Algebra l S -> Set _
   Hom {S = F , ρ} (A , 𝐹ᴬ) (B , 𝐹ᴮ) =
       ∃ λ (f : A -> B) -> (𝓸 : F) (𝒂 : ρ 𝓸 -> A)
	-----------------------------------------
	 ->    f (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᴮ 𝓸 (f ∘ 𝒂)

   id : (𝑨 : Algebra k S) -> Hom 𝑨 𝑨
   id (A , 𝑨) = (λ x -> x) , λ _ _ -> refl

   _>>>_ : {S : Signature i j} {𝑨 : Algebra k S}
	   {𝑩 : Algebra l S} {𝑪 : Algebra m S}
     ->    Hom 𝑨 𝑩  ->  Hom 𝑩 𝑪
	   ---------------------
     ->         Hom 𝑨 𝑪
   _>>>_ {S = F , ρ} {𝑨 = A , 𝐹ᴬ} {𝑪 = C , 𝐹ᶜ}
	 (f , α) (g , β) = g ∘ f , γ
	   where
	   γ :    (𝓸 : F) (𝒂 : ρ 𝓸 -> A)
		---------------------------------------
	     ->   (g ∘ f) (𝐹ᴬ 𝓸 𝒂) ≡ 𝐹ᶜ 𝓸 (g ∘ f ∘ 𝒂)
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

Next we define a type for congruence relations. For this we define functions that test whether a given operation or term is **compatible** with a given relation. The notions are defined in the file ``Con.agda``, the contents of which are shown below.

.. code-block:: agda

   {-# OPTIONS --without-K --exact-split #-}

   open import Preliminaries
   open import Basic 
   open import Hom

   module Con {i j k : Level} {S : Signature i j}  where

   -- lift a binary relation from pairs to pairs of tuples.
   lift-rel : ∀{ℓ₁ : Level} {Idx : Set ℓ₁} {ℓ₂ : Level} {Z : Set ℓ₂}
    ->         Rel Z ℓ₂
	    -----------------
    ->       Rel (Idx -> Z) (ℓ₁ ⊔ ℓ₂)
   lift-rel R = λ args₁ args₂ -> ∀ i -> R (args₁ i) (args₂ i)

   -- compatibility of a give function-relation pair
   compatible-fun : ∀ {ℓ₁ ℓ₂ : Level} {γ : Set ℓ₁} {Z : Set ℓ₂}
    ->             ((γ -> Z) -> Z)
    ->             (Rel Z ℓ₂)
		  -----------------------------------------
    ->             Set (ℓ₁ ⊔ ℓ₂)
   compatible-fun f 𝓻 = (lift-rel 𝓻) =[ f ]⇒ 𝓻

   -- relation compatible with an operation
   compatible : (𝑨 : Algebra k S)
    ->         ∣ S ∣
    ->         Rel ∣ 𝑨 ∣ k
	     -------------------------------
    ->         Set (j ⊔ k)
   compatible 𝑨 𝓸 𝓻 =
    (lift-rel {j} {⟦ S ⟧ 𝓸} {k} {∣ 𝑨 ∣}  𝓻) =[ (⟦ 𝑨 ⟧ 𝓸) ]⇒ 𝓻

   -- relation compatible with all operations of an algebra
   compatible-alg : (𝑨 : Algebra k S)
    ->            Rel ∣ 𝑨 ∣ k
		------------------------------
    ->             Set (i ⊔ j ⊔ k)
   compatible-alg 𝑨 𝓻 = ∀ 𝓸 -> compatible 𝑨 𝓸 𝓻

   -- Congruence relations
   Con : (𝑨 : Algebra k S)
	 -----------------------
    ->    Set (i ⊔ j ⊔ lsuc k)
   --  ->    Set (lsuc i ⊔ lsuc j ⊔ lsuc k)
   Con 𝑨 = ∃ λ (θ : Rel ∣ 𝑨 ∣ k)
	    -> IsEquivalence θ × compatible-alg 𝑨 θ

   con : (𝑨 : Algebra k S)
	 -----------------------
    ->   Pred (Rel ∣ 𝑨 ∣ k) _
   con 𝑨 = λ θ → IsEquivalence θ × compatible-alg 𝑨 θ
	  --  -> 
   record Congruence (𝑨 : Algebra k S) : Set (i ⊔ j ⊔ lsuc k) where
    constructor mkcon
    field
      ∥_∥ : Rel ∣ 𝑨 ∣ k
      Compatible : compatible-alg 𝑨 ∥_∥
      IsEquiv : IsEquivalence ∥_∥
   open Congruence 

   --a single θ-class of A
   [_]_ : {A : Set k} -> (a : A) -> Rel A k -> Pred A _
   [ a ] θ = λ x → θ a x

   --the collection of θ-classes of A
   _//_ : (A : Set k) -> Rel A k -> Set _
   A // θ = ∃ λ (C : Pred A _) -> (∃ λ a -> C ≡ [ a ] θ)


   _/_ : (𝑨 : Algebra k S)
    ->  Congruence 𝑨
       -----------------------
    ->  Algebra (lsuc k) S
   𝑨 / θ = ( ( ∣ 𝑨 ∣ // ∥ θ ∥ ) , -- carrier
	     ( λ 𝓸 args        -- operations
		 -> ( [ ⟦ 𝑨 ⟧ 𝓸 (λ i₁ -> ∣ ⟦ args i₁ ⟧ ∣) ] ∥ θ ∥ ) ,
		    ( ⟦ 𝑨 ⟧ 𝓸 (λ i₁ -> ∣ ⟦ args i₁ ⟧ ∣) , refl )
	     )
	   )

   _IsHomImageOf_ : (𝑩 : Algebra (lsuc k) S)
    ->             (𝑨 : Algebra k S)
    ->             Set _
   𝑩 IsHomImageOf 𝑨 =
    ∃ λ (θ : Rel ∣ 𝑨 ∣ k) -> con 𝑨 θ
      ->   (∣ 𝑨 ∣ // θ) ≃ ∣ 𝑩 ∣

   HomImagesOf : Algebra k S -> Pred (Algebra (lsuc k) S) (i ⊔ j ⊔ lsuc k)
   HomImagesOf 𝑨 = λ 𝑩 -> 𝑩 IsHomImageOf 𝑨 

   _IsHomImageOfClass_ : Algebra (lsuc k) S -> Pred (Algebra k S) k -> Set _
   𝑩 IsHomImageOfClass 𝓚 = ∃ λ 𝑨 -> 𝑨 ∈ 𝓚 -> 𝑩 IsHomImageOf 𝑨

   HomImagesOfClass : Pred (Algebra k S) k
     ->               Pred (Algebra (lsuc k) S) (i ⊔ j ⊔ lsuc k)
   HomImagesOfClass 𝓚 = λ 𝑩 -> ∃ λ 𝑨 -> 𝑨 ∈ 𝓚 -> 𝑩 IsHomImageOf 𝑨

----------------------------

In the next chapter we turn to the important topic of **terms** (the datatypes for which we have defined in the file ``free.agda``).

-----------------------------------------------


.. include:: hyperlink_references.rst



    
