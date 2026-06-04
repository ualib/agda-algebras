---
layout: default
title : "Overture.Functions module (The Agda Universal Algebra Library)"
date : "2026-05-07"
author: "the agda-algebras development team"
---

### <a id="functions">Foundational function infrastructure</a>

This is the [Overture.Functions][] module of the [Agda Universal Algebra Library][].

This module collects the foundational definitions concerning raw functions `A → B` between bare types that are needed by the canonical `Setoid/` tree.  All the definitions here take their arguments at the level of bare types and raw functions; none presupposes a setoid structure.  The setoid-respecting analogues — image and surjectivity for setoid functions `𝐴 ⟶ 𝐵` — live in `Setoid.Functions.*` and are independent.  The two coexist because they have genuinely different type signatures and serve genuinely different call sites.

The contents fall into three clusters.

+  **Image and inverse**.  An inductive type `Image f ∋ b` representing the image of a raw function as the existence of a preimage, together with the `Inv` operation that extracts a preimage from an inhabitant of that type.  The inductive presentation lets us *compute* a range-restricted inverse, which is what surjectivity needs.
+  **Surjectivity**.  A predicate `IsSurjective f`, the right-inverse `SurjInv`, the right-inverse-correctness lemma `SurjInvIsInverseʳ`, and the composition law `epic-factor` (used in the homomorphism factorization theorem in `Setoid.Homomorphisms.Factor`).
+  **Coordinate projection**.  Given an indexed family `B : I → Type b` over a type `I` with decidable equality, the projection `proj j : (∀ i → B i) → B j` and its surjectivity proof `projIsOnto`.  Used in `Setoid.Algebras.Products` to witness that the carrier-level projection from a product algebra onto a single factor is a surjection — a bare-types claim about raw functions, even though it sits inside the Setoid tree.  (A setoid-respecting upgrade is tracked as a follow-up to #303.)

This module is a Category-A relocation under #303 (M2-6).  See [`src/Legacy/Base/DEPRECATED.md`](../Legacy/Base/DEPRECATED.md) for the full inventory and migration guidance.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Overture.Functions where

-- Imports from Agda primitives and the standard library.
open import Agda.Primitive    using ()           renaming ( Set to Type )
open import Data.Empty        using ( ⊥-elim )
open import Data.Product      using ( Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Function          using ( _∘_ ; _$_ ; Surjective )
open import Level             using ( Level ; _⊔_ )
open import Relation.Binary   using ( Decidable )
open import Relation.Nullary  using ( Dec ; yes ; no )

open import Axiom.UniquenessOfIdentityProofs  using ( module Decidable⇒UIP )
open import Relation.Binary.PropositionalEquality
                              using ( _≡_ ; refl ; sym ; trans ; cong ; cong-app )

-- Imports from agda-algebras.
open import Overture.Basic  using ( _≈_ ; _∙_ ; transport )

private variable a b c ι : Level
```

#### <a id="image">The image of a raw function</a>

The *image* of a raw function `f : A → B` at a point `b : B` is the proposition that some `a : A` satisfies `f a ≡ b`.  We represent it as an inductive type with one constructor, `eq`, which packages the witness `a` together with the equality proof.  This inductive presentation matters: an inhabitant of `Image f ∋ b` carries an actual point of `A`, so we can extract that point computationally (the function `Inv` below).  The corresponding Σ-type formulation `Σ[ a ∈ A ] f a ≡ b` would be logically equivalent but syntactically less convenient at the call sites; the legacy module has used the inductive form throughout, and the canonical Setoid tree consumes it that way.

```agda
module _ {A : Type a}{B : Type b} where

 data Image_∋_ (f : A → B) : B → Type (a ⊔ b) where
  eq : {b : B} → ∀ a → b ≡ f a → Image f ∋ b
```

Given an inhabitant of `Image f ∋ b`, we recover the underlying preimage by pattern matching on `eq`.  This is the `Inv` function, a *range-restricted* inverse: it is defined exactly on those `b : B` that are demonstrably in the image of `f`.

```agda
 Inv : (f : A → B){b : B} → Image f ∋ b → A
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : A → B}{b : B}(q : Image f ∋ b) → f (Inv f q) ≡ b
 InvIsInverseʳ (eq _ p) = sym p
```

#### <a id="surjectivity">Surjectivity of raw functions</a>

A raw function `f : A → B` is *surjective* when every `b : B` is in the image of `f`.  The library distinguishes this from stdlib's `Function.Surjective`, which is a more general "respects two arbitrary equivalences" notion; the bare-types `IsSurjective` is the specialization to propositional equality on both sides.  Conversion in either direction is straightforward, as the two helper lemmas below show.

```agda
module _ {A : Type a}{B : Type b} where

 IsSurjective : (A → B) → Type (a ⊔ b)
 IsSurjective f = ∀ y → Image f ∋ y

 IsSurjective→Surjective :  (f : A → B) → IsSurjective f
  →                         Surjective _≡_ _≡_ f
 IsSurjective→Surjective f fE y = goal
  where
  imgfy→A : Image f ∋ y → Σ[ x ∈ A ] f x ≡ y
  imgfy→A (eq x p) = x , sym p
  goal : Σ[ x ∈ A ] ({z : A} → z ≡ x → f z ≡ y)
  goal = proj₁ (imgfy→A $ fE y)
       , λ z≡fst → trans (cong f z≡fst) $ proj₂ (imgfy→A $ fE y)

 Surjective→IsSurjective :  (f : A → B) → Surjective {A = A} _≡_ _≡_ f
  →                         IsSurjective f
 Surjective→IsSurjective f fE y = eq (proj₁ $ fE y) (sym $ proj₂ (fE y) refl)
```

A right-inverse of a surjective `f` is obtained by composing `Inv` with the surjectivity proof.  The right-inverse property is then immediate from `InvIsInverseʳ` above.

```agda
 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE = Inv f ∘ fE

 SurjInvIsInverseʳ :  (f : A → B)(fE : IsSurjective f)
  →                   ∀ b → f ((SurjInv f fE) b) ≡ b
 SurjInvIsInverseʳ f fE b = InvIsInverseʳ (fE b)
```

The composition law for surjective functions: if `f` factors through `g` via `h`, and `f` is surjective, then so is `h`.  This is consumed in `Setoid.Homomorphisms.Factor` to lift surjectivity through the homomorphism factorization diagram.

```agda
module _ {A : Type a}{B : Type b}{C : Type c} where

 epic-factor :  (f : A → B)(g : A → C)(h : C → B)
  →             f ≈ h ∘ g → IsSurjective f → IsSurjective h
 epic-factor f g h compId fe y = goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : y ≡ f (finv y)
   ζ = sym (SurjInvIsInverseʳ f fe y)

   η : y ≡ (h ∘ g) (finv y)
   η = ζ ∙ compId (finv y)

   goal : Image h ∋ y
   goal = eq (g (finv y)) η

 epic-factor-intensional :  (f : A → B)(g : A → C)(h : C → B)
  →                         f ≡ h ∘ g → IsSurjective f → IsSurjective h
 epic-factor-intensional f g h compId fe y = goal
  where
   finv : B → A
   finv = SurjInv f fe

   ζ : f (finv y) ≡ y
   ζ = SurjInvIsInverseʳ f fe y

   η : (h ∘ g) (finv y) ≡ y
   η = (cong-app (sym compId) (finv y)) ∙ ζ

   goal : Image h ∋ y
   goal = eq (g (finv y)) (sym η)
```

#### <a id="projection">Coordinate projection out of a dependent product</a>

Given an indexed family `B : I → Type b` and a "default" point `bs₀ : ∀ i → B i` of the dependent product, we define the coordinate projection `proj j` and prove it surjective.  The default point and the decidable equality on `I` are both essential: without a fallback value at indices `i ≠ j` we cannot construct a preimage of an arbitrary `b : B j`, and without decidable equality we cannot decide which coordinate to fill in with `b`.

The auxiliary `update` modifies the default point at the single coordinate `j` to take a given value `b`, leaving the other coordinates alone.  The auxiliary `update-id` says that `update bs₀ (j , b)` evaluated at `j` gives back `b`, regardless of which proof of `j ≡ j` the decision procedure happens to produce.  The latter is where uniqueness-of-identity-proofs (UIP) for the index type `I` enters: `update-id` cannot be proved without it, because the "yes" case has to handle a propositionally-but-not-definitionally trivial equality proof.  The `Decidable⇒UIP` module from stdlib gives us UIP for any type with decidable equality, which is the assumption already made on `I`.

```agda
module _  {I : Type ι}(_≟_ : Decidable {A = I} _≡_)
          {B : I → Type b}
          (bs₀ : ∀ i → B i)
 where
 open Decidable⇒UIP _≟_ using ( ≡-irrelevant )

 proj : (j : I) → (∀ i → B i) → B j
 proj j xs = xs j

 update : (∀ i → B i) → ((j , _) : Σ I B) → (∀ i → Dec (i ≡ j) → B i)
 update _   (_ , b)  i (yes x)  = transport B (sym x) b
 update bs  _        i (no  _)  = bs i

 update-id : ∀{j b} → (c : Dec (j ≡ j)) → update bs₀ (j , b) j c ≡ b
 update-id {j} {b}  (yes p) = cong (λ x → transport B x b)
                                   (≡-irrelevant (sym p) refl)
 update-id          (no ¬p) = ⊥-elim (¬p refl)

 proj-is-onto : ∀{j} → Surjective {A = ∀ i → B i} _≡_ _≡_ (proj j)
 proj-is-onto {j} b = bs , λ x → trans (cong (λ u → proj j u) x) pf
  where
  bs : (i : I) → B i
  bs i = update bs₀ (j , b) i (i ≟ j)

  pf : proj j bs ≡ b
  pf = update-id (j ≟ j)

 projIsOnto : ∀{j} → IsSurjective (proj j)
 projIsOnto {j} = Surjective→IsSurjective (proj j) proj-is-onto
```

--------------------------------------

<span style="float:left;">[← Overture.Relations](Overture.Relations.html)</span>
<span style="float:right;">[Overture.Terms →](Overture.Terms.html)</span>

{% include UALib.Links.md %}
