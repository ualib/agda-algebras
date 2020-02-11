--File: preliminaries.agda
--AUTHOR: William DeMeo
--DATE: 27 Dec 2019
--UPDATED: 22 Jan 2019
--
--NOTES
--
-- The code in this file is based on the following Agda tutorials:
--
--   Thorsten Altenkirk (http://www.cs.nott.ac.uk/~psztxa/g53cfr/l05.html/l05.html)
--   Bove and Dybjer (http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)
--   Páli Gábor János (https://people.inf.elte.hu/pgj/agda/tutorial/Index.html)
--   Norell and Chapman (http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf)
--   Wadler (https://plfa.github.io/)

open import Level
--open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

module preliminaries where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Function
open import Agda.Builtin.Nat public
  renaming ( Nat to ℕ; _-_ to _∸_; zero to nzero; suc to succ )
--  using    ( _+_; _*_ )
----------------------------------------------------------------------

---------------
--BOOLEAN Type
---------------

data Bool : Set where
  true : Bool
  false : Bool

----------------------------------------------------------------------

----------------------------
--FUNCTION COMPOSITION Def
----------------------------
-- infixr 40 _∘_

------------------
--Basic version
-- _∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
-- g ∘ f = λ x -> g (f x)

-----------------------
--More general version
-- _∘_ : {A : Set}{B : A -> Set}
--       {C : (x : A) -> B x -> Set}
--       (f : {x : A}(y : B x) -> C x y)
--       (g : (x : A) -> B x)   (x : A)
--     ------------------------------------
--   ->  C x (g x)

-- (f ∘ g) x = f (g x)

----------------------------
--Even more general version
-- _∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
--   -> (B -> C) -> (A -> B) -> A -> C
-- (g ∘ f) x = g (f x)

----------------------------------------------------------------------


------------------
--SET ISOMORPHISM
-------------------

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A

    --from is left-inv for to
    from∘to : ∀ (x : A) -> from (to x) ≡ x

    --from is right-inv for to
    to∘from : ∀ (y : B) -> to (from y) ≡ y  

open _≃_

-------------------------------------------------------------------

-------------------------------
--ISOMORPHISM IS AN EQUIVALENCE
-------------------------------
--Isomorphism is an equivalence (reflexive, symmetric, transitive).
--To show reflexivity, take both to and from to be the identity function.
≃-refl : ∀ {A : Set}
         ----------
  ->      A ≃ A

≃-refl =
  record
    {
      to      = λ{x -> x};
      from    = λ{y -> y};
      from∘to = λ{x -> refl};
      to∘from = λ{y -> refl}
    }  

≃-sym : ∀ {A B : Set}
  ->    A ≃ B
        ------
  ->    B ≃ A
≃-sym A≃B =
  record
    {
    to = from A≃B;
    from = to A≃B;
    from∘to = to∘from A≃B;
    to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set}
  ->      A ≃ B  ->  B ≃ C
          ----------------
  ->      A ≃ C
≃-trans A≃B B≃C =
  record
    {
    to      = to B≃C ∘ to A≃B ;
    from    = from A≃B ∘ from B≃C ;
    from∘to = λ {x ->
      begin -- Goal: (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x) ≡ x
        from A≃B ((from B≃C ∘ to B≃C) ((to A≃B) x))
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
        from A≃B (to A≃B x)
      ≡⟨ from∘to A≃B x ⟩
        x
      ∎} ;
    to∘from = λ {y ->
      begin -- Goal: (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y) ≡ y
        to B≃C (to A≃B (from A≃B (from B≃C y)))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
        to B≃C (from B≃C y)
      ≡⟨ to∘from B≃C y ⟩
        y
      ∎}
    }

-----------------------------------------------------------------------

--------------------------------------
--Reasoning for Isomorphism
--------------------------------------
--Here's a variant of equational reasoning for isomorphism.
--The form that corresponds to _≡⟨⟩_ is omitted, since trivial
--isomorphisms arise far less often than trivial equalities.

--Chains of Set isomorphisms
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    ->     A ≃ B
           -----
    ->     A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (x : Set) {y z : Set}
    ->    x ≃ y  ->  y ≃ z
          ----------------
    ->     x ≃ z
  x ≃⟨ x≃y ⟩ y≃z = ≃-trans x≃y y≃z

  _≃-∎ : ∀ (x : Set)
         ---------
    ->   x ≃ x
  x ≃-∎ = ≃-refl

open ≃-Reasoning

---------------------------------------------------------

------------------------------
--SUBSETS (embedding) record
------------------------------

--Embedding shows that the first type is included in the second.
infix 0 _≲_

-- record _≲_ {ℓ : Level} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
--   field
--     to   : A -> B
--     from : B -> A
--     from∘to : ∀ (x : A) -> from (to x) ≡ x

record _≲_ (A : Set) (B : Set) : Set where
  field
    to   : A -> B
    from : B -> A
    from∘to : ∀ (x : A) -> from (to x) ≡ x

open _≲_

--Embedding is a preorder (reflexive and transitive)
≲-refl : ∀ {A : Set}
        ------------
  ->      A ≲ A

≲-refl =
  record {
    to = λ x -> x ;
    from = λ x -> x ;
    from∘to = λ x -> refl
  }

≲-trans : ∀ {A B C : Set}
  ->      A ≲ B  ->  B ≲ C
         ------------------
  ->          A ≲ C

≲-trans A≲B B≲C =
  record {
    to   = to B≲C ∘ to A≲B ;
    from = from A≲B ∘ from B≲C ;
    from∘to = λ x ->
      begin -- Goal: (from A≲B ∘ from B≲C) ((to B≲C ∘ to A≲B) x) ≡ x
        from A≲B (from B≲C (to B≲C (to A≲B x)))
      ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x))  ⟩
        from A≲B (to A≲B x)
      ≡⟨ from∘to A≲B x ⟩
        x
      ∎
  }

--------------------------------
--REASONING with the ≲ relation
--------------------------------

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    ->     A ≲ B
           -----
    ->     A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (x : Set) {y z : Set}
    ->    x ≲ y  ->  y ≲ z
          ----------------
    ->     x ≲ z
  x ≲⟨ x≲y ⟩ y≲z = ≲-trans x≲y y≲z


  _≲-∎ : ∀ (x : Set)
         ---------
    ->   x ≲ x
  x ≲-∎ = ≲-refl

open ≲-Reasoning

--------------------------------------------------------

--------------------------
--A PROP Type (called Prp)
--------------------------
-- module prop {ℓ : Level} where

  --We identify Prop and Set.
  --Prop is already reserved in Agda hence we use Prp instead.
Prp : Set₁
Prp = Set

  ----------------------------------------------------------------
  --IMPLICATION IS FUNCTION
  -------------------------
  -------------------------------
  --IMPLICATION Def. (⇒ = \=>)
  -------------------------------
  --We interpret implication as function space. 
  --We know that P ⇒ Q is true if we have a function
  --transforming proofs of P into proofs of Q.

_⇒_ : Prp -> Prp -> Prp
P ⇒ Q = P -> Q

infixr 0 _⇒_

  --A very simple tautology:
I : {P : Prp} -> P ⇒ P
I p = p

  --Given two propositions A and B, the implication A -> B holds if whenever
  --A holds then B also holds. We formalise implication using function type.

  --Evidence that A -> B holds is of the form `λ (x : A) -> y`
  --where y : B contains as a free variable x : A.

  --Given a term L providing evidence for A -> B, and a term M
  --providing evidence for A, the term L M provides evidence for B.

  --In other words, evidence for A -> B is a function that converts
  --evidence for A into evidence for B.  i.e., if we know that A -> B
  --and A both hold, then we know that B also holds.

->-elim : ∀ {A B : Set}

  ->      (A -> B)  ->  A
        ----------------
  ->           B

->-elim L M = L M

  --Defining a function, with a named definition or a lambda abstraction, is
  --IMPLICATION INTRODUCTION; applying a function is IMPLICATION ELIMINATION.

  --Implication elimination followed by implication introduction is the identity.

η--> : ∀ {A B : Set} (f : A -> B) -> (λ (x : A) -> f x) ≡ f
η--> f = refl

  --Implication binds less tightly than any other operator. Thus, A ⊎ B -> B ⊎ A
  --parses as (A ⊎ B) -> (B ⊎ A).

-- subset
_⊆_ : ∀ {X : Set} -> (A : X -> Prp) -> (B : X -> Prp) -> Prp
A ⊆ B = ∀ i -> A i ⇒ B i


  -------------------------------------------------------------

  ----------------------------------
  --CONJUNCTION Type  (∧ = \and)
  ----------------------------------
  --A proof of P ∧ Q is a pair of proofs one of P and one of Q.

  --The ∧-intro ("and introduction") rule.
data _∧_ (P Q : Prp) : Prp where

  _,_ :  P  ->  Q
       ------------
    ->    P ∧ Q

infixr 2 _∧_

  --The left ∧-elim ("and elimination") rule.
left : {P Q : Prp}

  ->   P ∧ Q
      --------
  ->    P
    
left (p , q) = p

  --The right ∧-elim ("and elimination") rule.
right : {P Q : Prp}

  ->   P ∧ Q
      --------
  ->    Q

right (p , q) = q

  --A simple tautology: ∧ is commutative.
comm-∧ : {P Q : Prp} -> P ∧ Q ⇒ Q ∧ P
comm-∧ (p , q) = q , p

  -------------------------------
  --DISJUNCTION Type (∨ = \or)
  -------------------------------
  --A proof of P ∨ Q is either a proof of P (prefixed with inl,
  --for "in left" or "left introduction") or a proof of Q
  --(prefixed with inr, for "in right").

data _∨_ (P Q : Prp) : Prp where

  inl :    P
        -------
    ->   P ∨ Q
      
  inr :    Q
        -------
    ->   P ∨ Q

infixr 1 _∨_

  -- ∨ is commutative
∨-comm : {P Q : Prp} -> P ∨ Q ⇒ Q ∨ P
∨-comm (inl p) = inr p
∨-comm (inr q) = inl q

  -- ∧ distributes over ∨
∧-distrib-∨-=> : {P Q R : Prp} -> P ∧ (Q ∨ R) ⇒ (P ∧ Q) ∨ (P ∧ R)
∧-distrib-∨-=> (p , inl q) = inl (p , q)
∧-distrib-∨-=> (p , inr r) = inr (p , r)

∧-distrib-∨-<= : {P Q R : Prp} -> (P ∧ Q) ∨ (P ∧ R) ⇒ P ∧ (Q ∨ R)
∧-distrib-∨-<= (inl (p , q)) = (p , inl q)
∧-distrib-∨-<= (inr (p , r)) = (p , inr r)

  -------------------------------------------
  --LOGICAL EQUIVALENCE Def (⇔ = \iff)
  -------------------------------------------
  --Define ⇔ in terms of ∧ and ⇒ 
_⇔_ : Prp -> Prp -> Prp
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

infixr 0 _⇔_

  --we can combine the two lemmas above to prove the distributivity 
  --as a logical equivalence.
∧-distrib-∨ : {P Q R : Prp} ->  P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
∧-distrib-∨ = ∧-distrib-∨-=> , ∧-distrib-∨-<=

  ---------------------------------------------------

  ------------------------
  --CONJUNCTION IS PRODUCT
  ------------------------

  --Given two propositions A and B, the conjunction A × B holds
  --if both A holds and B holds. We formalise this idea by
  --declaring a suitable inductive type.

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ : A  ->  B
         ---------
    ->    A × B

  --Evidence that A × B holds is of the form ⟨ M , N ⟩, where M
  --provides evidence that A holds and N provides evidence that B holds.

  --Given evidence that A × B holds, we can conclude that either A holds or B holds.

fst : ∀ {A B : Set}

  ->    A × B
         --------
  ->      A

fst ⟨ x , y ⟩ = x

snd : ∀ {A B : Set}
  ->    A × B
       -------
  ->    B
snd ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) -> ⟨ fst w , snd w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

  -- --Thus, m ≤ n × n ≤ p parses as (m ≤ n) × (n ≤ p).

comm-× : ∀ {A B : Set} -> A × B ≃ B × A
comm-× =
  record
    {
    to = λ {⟨ x , y ⟩ -> ⟨ y , x ⟩} ;
    from = λ {⟨ y , x ⟩ -> ⟨ x , y ⟩};
    from∘to = λ {⟨ x , y ⟩ -> refl} ;
    to∘from = λ {⟨ y , x ⟩ -> refl}
    }

assoc-× : ∀ {A B C : Set} -> (A × B) × C ≃ A × (B × C)
assoc-× =
  record
    {
    to = λ {⟨ ⟨ x , y ⟩ , z ⟩ -> ⟨ x , ⟨ y , z ⟩ ⟩} ;
    from = λ {⟨ x , ⟨ y , z ⟩ ⟩ -> ⟨ ⟨ x , y ⟩ , z ⟩ };
    from∘to = λ {⟨ ⟨ x , y ⟩ , z ⟩ -> refl } ;
    to∘from = λ {⟨ x , ⟨ y , z ⟩ ⟩ -> refl }
    }


  ----------------------------------------------------------------

  ---------------------
  --DISJUNCTION IS SUM
  ---------------------
  --Given two propositions A and B, the disjunction A ⊎ B holds if either A
  --holds or B holds. We formalise this idea by declaring a suitable inductive type.

data _⊎_ (A B : Set) : Set where

  inl :   A
        -------
    ->   A ⊎ B
       
  inr :   B
        -------
    ->   A ⊎ B
       
  --Evidence that A ⊎ B holds is either of the form inl M, where M provides
  --evidence that A holds, or inr N, where N provides evidence that B holds.

  --Given evidence that A -> C and B -> C both hold, then given evidence
  --that A ⊎ B holds we can conclude that C holds.

⊎-elim : ∀ {A B C : Set}

  ->     (A ⊎ B) -> (A -> C) -> (B -> C)
        ----------------------------------
  ->                  C

⊎-elim (inl a) f _ =  f a
⊎-elim (inr b) _ g =  g b


  --η-rule for ⊎
  --Applying ⊎-elim the each intro rule is the identity.
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) -> ⊎-elim w inl inr ≡ w
η-⊎ (inl x) = refl
η-⊎ (inr y) = refl

  --More generally, we can also throw in an arbitrary function from a disjunction.
uniq-⊎ : ∀ {A B C : Set}
         (h : A ⊎ B -> C) (w : A ⊎ B)
       ---------------------------------------
  ->     ⊎-elim w (h ∘ inl) (h ∘ inr) ≡ h w
uniq-⊎ h (inl x) = refl
uniq-⊎ h (inr y) = refl

  --We set the precedence of disjunction so that it binds less
  --tightly than any other declared operator.

infix 1 _⊎_

  --Thus, A × C ⊎ B × C parses as (A × C) ⊎ (B × C).

  --Sum on types is commutative and associative up to isomorphism.

  --⊎ COMMUTATIVITY (up to isomorphism)
comm-⊎-=> : ∀ {A B : Set} -> A ⊎ B -> B ⊎ A
comm-⊎-=> (inl x) = inr x
comm-⊎-=> (inr x) = inl x

involutive-comm-⊎ : ∀ {A B : Set} (x : A ⊎ B) -> comm-⊎-=> (comm-⊎-=> x) ≡ x
involutive-comm-⊎ (inl x) = refl
involutive-comm-⊎ (inr x) = refl

comm-⊎ : ∀ {A B : Set} -> A ⊎ B ≃ B ⊎ A
comm-⊎ =
  record
  {
  to = comm-⊎-=> ;
  from = comm-⊎-=> ;
  from∘to = involutive-comm-⊎ ;
  to∘from = involutive-comm-⊎
  }

  --⊎ ASSOCIATIVITY (up to isomorphism)
assoc-⊎-to : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C -> A ⊎ (B ⊎ C)
assoc-⊎-to (inl (inl x)) = inl x
assoc-⊎-to (inl (inr x)) = inr (inl x)
assoc-⊎-to (inr x) = inr (inr x)

assoc-⊎-from : ∀ {A B C : Set} -> A ⊎ (B ⊎ C) -> (A ⊎ B) ⊎ C
assoc-⊎-from (inl x) = inl (inl x)
assoc-⊎-from (inr (inl x)) = inl (inr x)
assoc-⊎-from (inr (inr x)) = inr x

assoc-⊎-from∘to-id : ∀ {A B C : Set} (x : (A ⊎ B) ⊎ C) -> assoc-⊎-from (assoc-⊎-to x) ≡ x
assoc-⊎-from∘to-id (inl (inl x)) = refl
assoc-⊎-from∘to-id (inl (inr x)) = refl
assoc-⊎-from∘to-id (inr x) = refl

assoc-⊎-to∘from-id : ∀ {A B C : Set} (x : A ⊎ (B ⊎ C)) -> assoc-⊎-to (assoc-⊎-from x) ≡ x
assoc-⊎-to∘from-id (inl x) = refl
assoc-⊎-to∘from-id (inr (inl x)) = refl
assoc-⊎-to∘from-id (inr (inr x)) = refl

assoc-⊎ : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
assoc-⊎ =
  record
    {
    to = assoc-⊎-to ;
    from = assoc-⊎-from ;
    from∘to = assoc-⊎-from∘to-id ;
    to∘from = assoc-⊎-to∘from-id
    }

  ----------------------------------------------------------------


  ----------------------------
  --EXTENSIONALITY Postulate
  ----------------------------
  --The only way to distinguish functions is by applying them; if two functions
  --applied to the same argument always yield the same result, then they are
  --the same function. It is the converse of cong-app.
  --
  --Agda DOES NOT PRESUME EXTENSIONALITY, but we can POSTULATE that it holds.
  --This postulate is okay since it's CONSISTENT with the theory underlying Agda.

  --------------------------------------
  --Ordinary function extensionality
postulate
  extensionality : ∀ {A B : Set} {f g : A -> B}
    ->             (∀ (x : A) -> f x ≡ g x)
                   ------------------------
    ->              f ≡ g
                   
  --------------------------------------
  --Dependent function extensionality
postulate
  ∀-extensionality :
    ∀ {A : Set} {B : A -> Set} {f g : ∀(x : A) -> B x}

    ->    ( ∀ (x : A)   ->   f x ≡ g x )
         --------------------------------
    ->               f ≡ g

  -------------------------------------------------------------
  --Dependent function extensionality (with product codomain)
postulate
  extensionality-dep-× :
    ∀ {A : Set} {B C : A -> Set} {f g : (x : A) -> B x × C x}
      ->             (∀ (x : A) -> fst (f x) ≡ fst (g x) -> snd (f x) ≡ snd (g x))
                   ---------------------------------------------------------------
      ->              f ≡ g


  ------------------------------
  --TRUE Type (⊤ = \top)
  ------------------------------
  --The trivially true proposition (type) has a trivial proof.
  --There is an introduction rule, but no elimination because we can't
  --get something for nothing.
  --We can view ⊤ as a special case of ∧ with no arguments. 
data ⊤ : Set where

  tt : ---
        ⊤

  --old definition
  -- data ⊤ : Prp where
  --   tt : ⊤

η-⊤ : ∀ (w : ⊤) ->  tt ≡ w
η-⊤ tt = refl

⊤-lidentity : ∀ {A : Set} -> ⊤ × A ≃ A
⊤-lidentity =
  record
    {
    to = λ { ⟨ tt , x ⟩ -> x };
    from = λ { x -> ⟨ tt , x ⟩ };
    from∘to = λ { ⟨ tt , x ⟩ -> refl };
    to∘from = λ y → refl
    }

⊤-ridentity : ∀ {A : Set} -> A × ⊤ ≃ A
⊤-ridentity {A} =
  ≃-begin  -- Goal: A × ⊤ ≃ A
    (A × ⊤)
  ≃⟨ comm-× ⟩
    (⊤ × A)
  ≃⟨ ⊤-lidentity ⟩
    A
  ≃-∎



  ------------------------------------------

  ----------------------------
  --FALSE Type (⊥ = \bot)
  ----------------------------
  --Has no introduction rule, but one elimination rule.
  --We can view ⊥ as a special case of ∨ with no arguments.
  --False ⊥ never holds. We formalise this idea by declaring an empty inductive type.
data ⊥ : Set where    --(old definition: data ⊥ : Prp where)

--⊥-elimination rule. From false anything follows.
⊥-elim : ∀ {A : Set}
  ->     ⊥
        ---
  ->     A
⊥-elim ()

  --alternatively, we might call this efq for "ex falso quod libet" (latin)
efq : {P : Prp} -> ⊥ -> P
efq ()

  --The nullary case of uniq-⊎ is uniq-⊥, which asserts that ⊥-elim is equal
  --to an arbitrary function from ⊥.

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

  --Using the absurd pattern asserts there are no possible values for w, so
  --the equation holds trivially.

  --We refer to ⊥ as the empty type. And, indeed, type ⊥ has no members.

  --For numbers, zero is the identity of addition. Correspondingly, empty is the
  --identity of the sum type (up to isomorphism).

  --Exercise ⊥-lidentity (recommended)
  --Show empty is the left identity of sums up to isomorphism.
  -- Your code goes here
⊥-to : ∀ {A : Set} -> ⊥ ⊎ A -> A
⊥-to (inl x) = ⊥-elim x
⊥-to (inr x) = x

⊥-from∘to-id : ∀ {A : Set} (x : ⊥ ⊎ A) -> inr (⊥-to x) ≡ x
⊥-from∘to-id (inl x) = ⊥-elim x
⊥-from∘to-id (inr x) = refl

⊥-lidentity : ∀ {A : Set} -> ⊥ ⊎ A ≃ A
⊥-lidentity =
  record
    {
    to = ⊥-to ;
    from = λ {x -> inr x} ;
    from∘to = ⊥-from∘to-id ;-- Goal: (x : ⊥ ⊎ .A) → (λ { x → inr x }) (⊥-to x) ≡ x
    to∘from = λ y → refl
    }


  ---------------------------
  --NEGATION Def (¬ = \neg)
  ---------------------------
  -- As usual, ¬ P is defined as P -> ⊥.
¬ : Prp -> Prp
¬ P = P -> ⊥

  {- Some basic facts about negation. -}

contradict : {P : Prp} -> ¬ (P ∧ ¬ P)
contradict (p , np) = np p
  --Explanation. Assume: (p, np). Prove false.
  --Consider the term np p. We have a function np: P -> ⊥
  --that takes a proof of P and outputs ⊥.
  --Apply this function to the term p (a proof of P)
  --to get ⊥ (≡ np p), as desired.

contrapos : {P Q : Prp} -> (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P
contrapos pq nq p = nq (pq p)
  --Explanation.
  --Assume: pq : P -> Q, and nq : ¬ Q, and p : P.
  --Prove: ⊥
  --Apply pq to p to get (pq p : Q), a proof of Q.
  --Apply np : Q -> ⊥ to the term (pq p) to get ⊥.

  {- Let's prove the de Morgan laws -}

deMorgan¬∨ : {P Q : Prp} -> ¬ (P ∨ Q) ⇒ ¬ P ∧ ¬ Q 
deMorgan¬∨ npq = (λ p -> npq (inl p)) , λ q -> npq (inr q)
  
deMorgan¬∧¬ : {P Q : Prp} -> (¬ P) ∧ (¬ Q) ⇒ ¬ (P ∨ Q)
deMorgan¬∧¬ (np , nq) (inl p) = np p
deMorgan¬∧¬ (np , nq) (inr q) = nq q
  
deMorgan¬∨¬ : {P Q : Prp} -> (¬ P) ∨ (¬ Q) ⇒ ¬ (P ∧ Q)
deMorgan¬∨¬ (inl np) (p , q) = np p
deMorgan¬∨¬ (inr nq) (p , q) = nq q

 

  ------------------------------------------------------------------

  --------------
  --EXPONENTIAL
  --------------
  --Given two types A and B, we refer to A -> B as the function space from A to B.

  --It is also sometimes called the exponential, with B raised to the A power.

  --Exponential on types share a property with exponential on numbers in that
  --many of the standard identities for numbers carry over to the types.

  --Corresponding to the law (p ^ n) ^ m  ≡  p ^ (n * m) we have the isomorphism
  --    A → (B → C)  ≃  (A × B) → C
  --Both types can be viewed as functions that, given evidence for A and B,
  --we can construct evidence from C. This isomorphism sometimes goes by the
  --name "currying." The proof of the right inverse requires extensionality.

currying : ∀ {A B C : Set} -> (A -> B -> C) ≃ (A × B -> C)
currying =
  record
    {
    to = λ {f -> λ { ⟨ x , y ⟩ -> f x y}} ;
    from = λ {f -> λ { x y -> f ⟨ x , y ⟩}} ;
    from∘to = λ f → refl ;
    to∘from = λ g → extensionality λ {⟨ x , y ⟩ → refl}
    }

  --Corresponding to the law (p * n) ^ m = (p ^ m) * (n ^ m)
  --we have the isomorphism:
  --  A → B × C  ≃  (A → B) × (A → C)
  --That is, "A implies B and C" is the same as "A implies B and A implies C"
  --The proof of left inverse requires both extensionality and the η-rule for products.

->-distrib-× : ∀ {A B C : Set} -> (A -> B × C)  ≃  (A -> B) × (A -> C)
->-distrib-× =
  record
    {
    to = λ f → ⟨ (λ x → fst (f x)) , (λ x → snd (f x)) ⟩ ;
    from = λ {⟨ f , g ⟩ -> λ x -> ⟨ f x , g x ⟩} ;
    from∘to = λ f → extensionality λ x → η-× (f x) ;
    to∘from = λ {⟨ f , g ⟩ -> refl}
  }


  ---------------------------------------------------------------------------

  ---------------------------------------------------
  --UNIVERSAL QUANTIFICATION Def (∀ = \all)
  ---------------------------------------------------
  --If we are given a set A, and a predicate P : A -> Prp,
  --then ∀' A P : Prop means that P a is true (inhabited) for all a:A.
  --A proof of this is a (depndent) function that assigns to each a:A
  --an element of P a.
∀' : (A : Set) -> (A -> Prp) -> Prp
∀' A P = (a : A) -> P a  

  --We use ∀' because ∀ is a reserved word in Agda.

  --We formalise universal quantification using the dependent function type,
  --which has appeared throughout this book.

∀-elim : ∀ {A : Set} {B : A -> Set}
  ->     (L : ∀ (x : A) -> B x)  ->  (M : A)
        --------------------------------------
  ->         B M
∀-elim  L M = L M

  --Lemma.
η-abs : ∀ {A : Set} {B C : A -> Set} (f : (x : A) -> B x × C x) -> (x : A) -> B x × C x
η-abs f = λ a -> ⟨ fst (f a) , snd (f a) ⟩

  --Lemma.
η-dep-× : ∀ {A : Set} {B C : A -> Set} (f : (x : A) -> B x × C x) -> (η-abs f) ≡ f
η-dep-× = λ f -> extensionality-dep-×  λ x x₁ -> refl

∀-distrib-× : ∀ {A : Set} {B C : A -> Set} ->
     (∀ (x : A) -> B x × C x) ≃ (∀ (x : A) -> B x) × (∀ (x : A) -> C x)
∀-distrib-× =
  record
    {
    to =  -- Goal: ((x : .A) → .B x) × ((x : .A) → .C x)
          -- have: p  : (x : .A) → .B x × .C x
          λ p -> ⟨ (λ x -> fst (p x)) , (λ x -> snd (p x)) ⟩ ;
  
    from = λ p a -> ⟨ (fst p) a , (snd p) a ⟩ ;

    from∘to =  -- f  : (x : .A) → .B x × .C x
               -- Goal: (λ a → ⟨ fst (f a) , snd (f a) ⟩) ≡ f
               λ f -> η-dep-× f ;

    to∘from = -- g  : ((x : .A) → .B x) × ((x : .A) → .C x)
              -- Goal: ⟨ (λ x → fst g x) , (λ x → snd g x) ⟩ ≡ g
              λ g -> η-× g
    }     

---------------------------------------------------------------------

--------------------------------
--Sigma (dependent pair) Type
-------------------------------

-- data Σ (A : Set) (B : A → Set) : Set where
--   _,_ : (a : A) → (b : B a) → Σ A B

--infixr 4 _,_


data ∑ (A : Set) (B : A -> Set) : Set where
  ⟨_,_⟩ : (x : A) -> B x -> ∑ A B

-- Σ-syntax = ∑
-- infix 2 ∑-syntax
-- syntax ∑-syntax A (λ x -> B) = ∑[ x ∈ A ] B

--Evidence that Σ[ x ∈ A ] B x holds is of the form ⟨ M , N ⟩ where M is a term
--of type A, and N is evidence that B M holds.

----------------------------------------
--EXISTENTIAL QUANTIFICATION (∃ = \ex)
----------------------------------------
--If we are given a set A, and a predicate P : A -> Prp, then ∃' A P : Prop
--will mean that P a is true (inhabited) for some a:A. A proof of this is a
--(depndent) pair (a , p) where a : A and p : P a is a proof that P a is true (inhabited).

data ∃' (A : Set)(P : A -> Prp) : Prp where
  _,_ : (a : A) -> P a -> ∃' A P

--Here's the definition on Set (instead of Prp).
∃ : ∀ {A : Set} (B : A -> Set) -> Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax {A} (λ x -> B) = ∃[ x ∈ A ] B

--If for every x : A we have B x -> C, and ∃(x : A) B x, then
--we may conclude that C holds.

∃-elim : ∀ {A : Set} {B : A -> Set} {C : Set}
  ->     (∀ x -> B x -> C)  ->  ∃[ x ∈ A ] B x
        -----------------------------------
  ->                  C
∃-elim f ⟨ x , y ⟩ = f x y

--This is a generalization of currying.
--Here f has type (∀ x -> B x -> C), or (∃[ x ] B x) -> C,
--(i.e., ∑ A B -> C) and ⟨ x , y ⟩ has type ∃[ x ] B x (i.e., ∑ A B),
--and we are saying that f can be applied to ⟨ x , y ⟩ as simply f x y.
  
--Indeed, there is an isomorphism.

∀∃-currying : ∀ {A : Set} {B : A -> Set} {C : Set}
  -> (∀ x -> B x -> C) ≃ (∃[ x ∈ A ] B x -> C)
∀∃-currying =
  record
    {
    to = λ{ f -> λ{ ⟨ x , y ⟩ -> f x y }} ;
    from = λ{ g -> λ{x -> λ{y -> g ⟨ x , y ⟩ }}} ;
    from∘to = λ{ f -> refl } ;
    to∘from = λ{ g -> extensionality  λ{ ⟨ x , y ⟩ -> refl }}
    }

--N.B. the code to establish the isomorphism is identical to that for implication.

----------------------------------------
--Exercise ∃-distrib-⊎ (recommended)
--Show that existentials distribute over disjunction:

-- postulate
--   ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
--     ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} ->
     ∃[ x ∈ A ] (B x ⊎ C x) ≃ (∃[ x ∈ A ] B x) ⊎ (∃[ x ∈ A ] C x)
∃-distrib-⊎ =
  record
    {
    to = λ{ ⟨ x , inl y ⟩ -> inl ⟨ x , y ⟩;
            ⟨ x , inr y ⟩ -> inr ⟨ x , y ⟩ };
    from = λ{ (inl ⟨ x , y ⟩) -> ⟨ x , inl y ⟩;
              (inr ⟨ x , y ⟩) -> ⟨ x , inr y ⟩ };
    from∘to = λ{ ⟨ x , inl y ⟩ -> refl;
                 ⟨ x , inr y ⟩ -> refl } ;
    to∘from = λ{ (inl ⟨ x , y ⟩) -> refl ;
                 (inr ⟨ x , y ⟩) -> refl }
    }






--Sec 2.4 Datatype families

data Image_∋_  {A : Set} {B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

-- data Image_∋_ {ℓ : Level} {A B : Set ℓ}(f : A -> B) : B -> Set (suc ℓ) where
--   im : (x : A) -> Image f ∋ f x

-- data Image_∋_ {ℓ : Level} {A B : Set ℓ}(f : A -> B) : B -> Set ℓ where
--   im : (x : A) -> Image f ∋ f x

--N.B. the assertion Image f ∋ y must come with a proof, which is of the
--form ∃a f a = y, so we have a witness, so the inverse can be "computed"
--in the following way:
inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x  -- Cool!!!

-------------------------------------------------------------------


-------------------
--LIST Type
-------------------
--
infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

-- data List' {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
--   [] : List' A
--   _::_ : A -> List' A -> List' A

identity : ∀{ℓ : Level} (A : Set ℓ) -> A -> A
identity A x = x

apply : (A : Set)(B : A -> Set) ->
        ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

--list addition (i.e., concatenation)
_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


foldleft : {A B : Set} -> List A -> B -> (B -> A -> B) -> B
foldleft [] z f = z
foldleft (x :: l) z f = foldleft l (f z x) f

--brief sanity check of foldleft
testlist : List ℕ
testlist = 0 :: (1 :: (2 :: []))
x = foldleft testlist 0 _+_
--type C-c C-n x to see that the result is 3, as expected.






