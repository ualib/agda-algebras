{-
layout: default
title : Relations.Extensionality module (The Agda Universal Algebra Library)
date : 2021-02-23
author: [agda-algebras development team][]
-}

-- Relation Extensionality
-- =======================
-- This is the [Relations.Extensionality][] module of the [Agda Universal Algebra Library][].

{-# OPTIONS --without-K --exact-split --safe #-}

module Relations.Extensionality where

open import stdlib-imports

open import Overture.Preliminaries using (𝑖𝑑; _⁻¹; _∙_; transport)
open import Overture.Inverses using (IsSurjective; SurjInv; InvIsInv; Image_∋_; eq)
open import Relations.Discrete using (Op)
open import Relations.Quotients using ([_]; /-subset; /-supset; IsBlock; ⟪_⟫)
open import Relations.Truncation using (blk-uip; to-Σ-≡)

private variable 𝓤 𝓥 𝓦 𝓩 : Level


-- Function Extensionality
-- -----------------------
-- Previous versions of [UniversalAlgebra][] made heavy use of a *global function extensionality principle*.
-- This asserts that function extensionality holds at all universe levels. However, we decided to remove all
-- instances of global function extensionality from the latest version of the library and limit ourselves to
-- local applications of the principle. This has the advantage of making transparent precisely how and where
-- the library depends on function extensionality. The price we pay for this precision is a library that is
-- littered with extensionality postulates. Eventually we will probably remove these postulates in favor of an
-- alternative approach to extensionality, or even remove the need for it altogether.
--
-- Note that the next proof requires function extensionality, which we postulate in the module declaration.

module _ {fe : funext 𝓦 𝓦}{A : Type 𝓤}{B : Type 𝓦} where

 SurjInvIsRightInv : (f : A → B)(fE : IsSurjective f) → f ∘ (SurjInv f fE) ≡ 𝑖𝑑 B
 SurjInvIsRightInv f fE = fe (λ x → InvIsInv f (fE x))

-- We can also prove the following composition law for epics.

 epic-factor : {C : Type 𝓩}(f : A → B)(g : A → C)(h : C → B)
  →            f ≡ h ∘ g → IsSurjective f → IsSurjective h

 epic-factor f g h compId fe y = γ
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = cong-app (SurjInvIsRightInv f fe) y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (compId ⁻¹)(finv y)) ∙ ζ

   γ : Image h ∋ y
   γ = eq (g (finv y)) (η ⁻¹)


-- An alternative way to express function extensionality
-- -----------------------------------------------------
-- A useful alternative for expressing dependent function extensionality, which is essentially equivalent to
-- `dfunext`, is to assert that the `happly` function is actually an *equivalence*.
--
-- The principle of *proposition extensionality* asserts that logically equivalent propositions are
-- equivalent.  That is, if `P` and `Q` are propositions and if `P ⊆ Q` and `Q ⊆ P`, then `P ≡ Q`. For our
-- purposes, it will suffice to formalize this notion for general predicates, rather than for propositions
-- (i.e., truncated predicates).

pred-ext : (𝓤 𝓦 : Level) → Type (lsuc (𝓤 ⊔ 𝓦))
pred-ext 𝓤 𝓦 = ∀ {A : Type 𝓤}{P Q : Pred A 𝓦 } → P ⊆ Q → Q ⊆ P → P ≡ Q

-- Note that `pred-ext` merely defines an extensionality principle. It does not postulate that the principle
-- holds.  If we wish to postulate `pred-ext`, then we do so by assuming that type is inhabited (see
-- `block-ext` below, for example).

-- Quotient extensionality
-- -----------------------
-- We need an identity type for congruence classes (blocks) over sets so that two different presentations of
-- the same block (e.g., using different representatives) may be identified.  This requires two postulates:
-- (1) *predicate extensionality*, manifested by the `pred-ext` type; (2) *equivalence class truncation* or
-- "uniqueness of block identity proofs", manifested by the `blk-uip` type defined in the
-- [Relations.Truncation][] module. We now use `pred-ext` and `blk-uip` to define a type called
-- `block-ext|uip` which we require for the proof of the First Homomorphism Theorem presented in
-- [Homomorphisms.Noether][].

module _ {A : Type 𝓤}{R : Rel A 𝓦} where

 block-ext : pred-ext 𝓤 𝓦 → IsEquivalence R → {u v : A} → R u v → [ u ]{R} ≡ [ v ]{R}
 block-ext pe Req {u}{v} Ruv = pe (/-subset Req Ruv) (/-supset Req Ruv)


 private
   to-subtype|uip : blk-uip A R → {C D : Pred A 𝓦}{c : IsBlock C {R}}{d : IsBlock D {R}}
    →               C ≡ D → (C , c) ≡ (D , d)

   to-subtype|uip buip {C}{D}{c}{d}CD = to-Σ-≡(CD , buip D(transport(λ B → IsBlock B)CD c)d)

 block-ext|uip : pred-ext 𝓤 𝓦 → blk-uip A R → IsEquivalence R → ∀{u}{v} → R u v → ⟪ u ⟫ ≡ ⟪ v ⟫
 block-ext|uip pe buip Req Ruv = to-subtype|uip buip (block-ext pe Req Ruv)


-- Strongly well-defined operations
-- --------------------------------
-- We now describe an extensionality principle that seems weaker than function extensionality, but still
-- (probably) not provable in [MLTT][]. (We address this and other questions  below.)  We call this the
-- principle *strong well-definedness of operations*. We will encounter situations in which this weaker
-- extensionality principle suffices as a substitute for function extensionality.
--
-- Suppose we have a function whose domain is a function type, say, `I → A`.  For example, inhabitants of the
-- type `Op` defined above are such functions.  (Recall, the domain of inhabitants of type
-- `Op I A := (I → A) → A` is `I → A`.)
--
-- Of course, operations of type `Op I A` are well-defined in the sense that equal inputs result in equal
-- outputs.


welldef : {A : Type 𝓤}{I : Type 𝓥}(f : Op I A) → ∀ u v → u ≡ v → f u ≡ f v
welldef f u v refl = refl


-- A stronger form of well-definedness of operations is to suppose that point-wise equal inputs lead to the
-- same output.  In other terms, we could suppose that  for all `f : Op I A`, we have `f u ≡ f v` whenever `∀
-- i → u i ≡ v i` holds.  We call this formalize this notation in the following type.


swelldef : (𝓥 𝓤 : Level) → Type (lsuc (𝓤 ⊔ 𝓥))
swelldef 𝓥 𝓤 = ∀ {A : Type 𝓤}{I : Type 𝓥}(f : Op I A)(u v : I → A) → (∀ i → u i ≡ v i) → f u ≡ f v

private
  funext→swelldef : {𝓤 𝓥 : Level} → funext 𝓥 𝓤 → swelldef 𝓥 𝓤
  funext→swelldef fe f u v ptweq = γ
   where
   uv : u ≡ v
   uv = fe ptweq
   γ : f u ≡ f v
   γ = welldef f u v uv

---------------------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
