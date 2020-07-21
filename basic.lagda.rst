.. FILE      : basic.lagda.rst
.. AUTHOR    : William DeMeo and Siva Somayyajula
.. DATE      : 24 Dec 2019
.. UPDATED   : 21 Jul 2020
.. COPYRIGHT : (c) 2020 William DeMeo

.. Note: This was used for the second part of my talk at JMM Special Session.


.. _types for algebras:

Types for Algebras
===================

This chapter describes the `basic module`_ of the `agda-ualib`_ , which begins our Agda_ formalization of the basic concepts and theorems of universal algebra. In this module we will codify such notions as operation, :term:`signature`, and :term:`algebraic structure <algebra>`.

-----------------------------------

.. _preliminaries:

Preliminaries
-------------------------

Like most Agda programs, this one begins with some options and imports.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣;
    _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Π; _≡_)


:Unicode Hints: In agda2-mode_ type ``\MCI``, ``\MCU\_0``, ``\sqcup``, ``\b0`` and ``\b2`` to obtain 𝓘, 𝓤₀, ⊔, 𝟘, and 𝟚, respectively.


Then we begin the module called ``basic`` using Agda's ``module`` directive.

::

  module basic where

This is the second module of the `agda-ualib`_ , coming after ``prelude`` (the module that was described in :numref:`agda preliminaries`).

-----------------------------------

.. _operation type:

Operation type
--------------

We define the type of **operations**, and give an example (the projections).

::

  --The type of operations
  Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  Op I A = (I → A) → A

  --Example. the projections
  π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
  π i x = x i


The type ``Op`` encodes the arity of an operation as an arbitrary type ``I : 𝓥 ̇``, which gives us a very general way to represent an operation as a function type with domain ``I → A`` (the type of "tuples") and codomain ``A``.

The last two lines of the code block above codify the ``i``-th ``I``-ary projection operation on ``A``.

----------------------------------

.. _signature type:

Signature type
----------------

We define the signature of an algebraic structure in Agda like this.

::

  --𝓞 is the universe in which operation symbols live
  --𝓥 is the universe in which arities live
  Signature : (𝓞 𝓥 : Universe) → 𝓞 ⁺ ⊔ 𝓥 ⁺ ̇
  Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇  , ( F → 𝓥 ̇ )

In the `prelude module`_ we defined the syntax ∣_∣ and ∥_∥ for the first and second projections, resp.  Consequently, if ``𝑆 : Signature 𝓞 𝓥`` is a signature, then

  ∣ 𝑆 ∣ denotes the set of operation symbols (which is often called 𝐹), and

  ∥ 𝑆 ∥ denotes the arity function (which is often called ρ).

Thus, if  𝑓 : ∣ 𝑆 ∣  is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity of 𝑓.


-----------------------------------

.. _algebras in agda:

Algebras in Agda
------------------

Finally, we are ready to define the type of algebras in the signature ``S`` (which we also call "S-algebras").

::

  Algebra : (𝓤 : Universe) → {𝓞 𝓥 : Universe}
   →        (𝑆 : Signature 𝓞 𝓥) →  𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓞 ̇
  Algebra 𝓤 {𝓞}{𝓥} 𝑆 = Σ A ꞉ 𝓤 ̇ , ((𝑓 : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ 𝑓) A)

Thus, algebras in the signature 𝑆 (or 𝑆-algebras) inhabit the type ``Algebra 𝓤 {𝓞}{𝓥} 𝑆``. (Here, 𝓤 is the universe level of the type of carriers (or "universes") of 𝑆-algebras.)

As an alternative to this syntax---one that may seem more in line with the standard literature---we could write the last line above as

.. code-block::

  Algebra 𝓤 {𝓞} {𝓥} (F , ρ) = Σ A ꞉ 𝓤 ̇ ,  ((𝑓 : F )  → Op (ρ 𝑓) A )

Here ``𝑆 = (F , ρ)`` is the signature with ``F`` the set of operation symbols and ρ the arity function.

Throughout the library, we adopt the (less standard, but more convenient) notations 𝑓 : ∣ 𝑆 ∣ for an operation symbol of the signature 𝑆, and ∥ 𝑆 ∥ 𝑓 for the arity of that symbol.

Example
~~~~~~~~~~

A monoid signature has two operation symbols, say, ``e``  and ``·``, of arities 0 and 2 (thus, of types ``(𝟘 → A) → A`` and ``(𝟚 → A) → A``), resp.

::

  data monoid-op : 𝓤₀ ̇ where
   e : monoid-op
   · : monoid-op

  monoid-sig : Signature _ _
  monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }


The types indicate that ``e`` is nullary (i.e., takes no arguments, equivalently, takes args of type ``𝟘 → A``), while ``·`` is binary (as indicated  by argument type ``𝟚 → A``).

We will have more to say about the type of algebras later.  For now, we continue defining the syntax used in the ``agda-ualib`` to represent the basic objects of universal algebra.


Syntactic sugar for operation interpretation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Before proceding, we define some syntactic sugar that allows us to replace ∥ 𝑨 ∥ 𝑓 with slightly more standard-looking notation, 𝑓 ̂ 𝑨, where f is an operation symbol of the signature 𝑆 of 𝑨.

::

  module _ {𝑆 : Signature 𝓞 𝓥}  where

   _̂_ : (𝑓 : ∣ 𝑆 ∣)
    →   (𝑨 : Algebra 𝓤 𝑆)
    →   (∥ 𝑆 ∥ 𝑓  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

   𝑓 ̂ 𝑨 = λ x → (∥ 𝑨 ∥ 𝑓) x

   infix 40 _̂_

We can now write 𝑓 ̂ 𝑨 for the interpretation of the basic operation symbol 𝑓 in the algebra 𝑨.

:N.B.: Below, we will need slightly different notation, namely, 𝑡 ̇ 𝑨, to represent the interpretation of a :term:`term` 𝑡 in the algebra 𝑨.

(In future releases of the agda-ualib_ we may reconsider making it possible to use the same notation interpretations of operation symbols and terms.)

-------------------------------------------------------

.. _products of algebras:

Products of algebras
--------------------

The (indexed) product of a collection of algebras is also an algebra if we define such a product as follows:

::

  module _ {𝑆 : Signature 𝓞 𝓥}  where

   Π' : {I : 𝓘 ̇ }( 𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓤 ⊔ 𝓘) 𝑆
   Π' 𝒜 =  ((i : _) → ∣ 𝒜 i ∣) ,  λ 𝑓 x i → (𝑓 ̂ 𝒜 i) λ 𝓥 → x 𝓥 i

We have used an anonymous module here so that the (fixed) signature 𝑆 is available in the definition of the product without mentioning it explicitly.


-----------------------------------------------

Unicode Hints
---------------

Table of some special characters used in the `basic module`_.

  +--------+------------------------+
  | To get | Type                   |
  +--------+------------------------+
  | 𝒂, 𝒃   | ``\MIa``, ``\MIb``     |
  +--------+------------------------+
  | 𝒜      | ``\McA``               |
  +--------+------------------------+
  | 𝑓 ̂ 𝑨  |  ``\Mif \^ \MIA``      |
  +--------+------------------------+
  | ≅      | ``≅`` or ``\cong``     |
  +--------+------------------------+
  | ∘      | ``\comp`` or ``\circ`` |
  +--------+------------------------+
  | 𝒾𝒹     | ``\Mci\Mcd``           |
  +--------+------------------------+
  | ℒ𝒦     | ``\McL\McK``           |
  +--------+------------------------+
  | ϕ      | ``\phi``               |
  +--------+------------------------+

For a more complete list of symbols used in the agda-ualib_, see :numref:`unicode hints`.

Emacs commands for retrieving information about characters or the input method:

  * ``M-x describe-char`` (or ``M-m h d c``) with the cursor on the character of interest

  * ``M-x desscribe-input-method`` (or ``C-h I``) (for a list of unicode characters available in agda2-mode_)

------------------

.. include:: hyperlink_references.rst
