
These are the imports from the Agda standard library mentioned in Wadler's PLFA book.

1. Naturals: Natural numbers

   ```agda
   import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
   ```

2. Induction: Proof by induction

   ```agda
   import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
   ```

3. Relations: Inductive definition of relations

   ```agda
   import Data.Nat using (_≤_; z≤n; s≤s)
   import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;+-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
   ```
   
4.  Equality: Equality and equational reasoning

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
   ```

5. Isomorphism: Isomorphism and embedding

   ```agda
   import Function using (_∘_)
   import Function.Inverse using (_↔_)
   import Function.LeftInverse using (_↞_)
   ```

6. Connectives: Conjunction, disjunction, and implication


   ```agda
   import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
   import Data.Unit using (⊤; tt)
   import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
   import Data.Empty using (⊥; ⊥-elim)
   import Function.Equivalence using (_⇔_)
   ```

7. Negation: Negation, with intuitionistic and classical logic

   ```agda
   import Relation.Nullary using (¬_)
   import Relation.Nullary.Negation using (contraposition)
   ```

8. Quantifiers: Universals and existentials

   ```agda
   import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
   ```

9. Decidable: Booleans and decision procedures

   ```agda
   import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
   import Data.Nat using (_≤?_)
   import Relation.Nullary using (Dec; yes; no)
   import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
   import Relation.Nullary.Negation using (¬?)
   import Relation.Nullary.Product using (_×-dec_)
   import Relation.Nullary.Sum using (_⊎-dec_)
   import Relation.Binary using (Decidable)
   ```

10. Lists: Lists and higher-order functions

   ```agda
   import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
   import Data.List.All using (All; []; _∷_)
   import Data.List.Any using (Any; here; there)
   import Data.List.Membership.Propositional using (_∈_)
   import Data.List.Properties
	   using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
	   renaming (mapIsFold to map-is-foldr)
   import Algebra.Structures using (IsMonoid)
   import Relation.Unary using (Decidable)
   import Relation.Binary using (Decidable)
   ```
