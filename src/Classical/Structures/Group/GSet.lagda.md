---
layout: default
file: "src/Classical/Structures/Group/GSet.lagda.md"
title: "Classical.Structures.Group.GSet module"
date: "2026-07-11"
author: "the agda-algebras development team"
---

### The coset G-set as a unary algebra

This is the [Classical.Structures.Group.GSet][] module of the [Agda Universal Algebra Library][].

The transitive action of a group `G` on the coset space `G / H` is packaged here
as an ordinary *unary algebra*: the signature is
[`Sig-Unary`][Classical.Signatures.Unary] applied to the carrier of `G`
(one operation symbol per group element, each of arity one) and the algebra's
domain is the quotient setoid `cosetSetoid`{.AgdaFunction} of
[Classical.Structures.Group.Cosets][].  The symbol `g` acts by left translation,
`x ↦ g ∙ x`, which respects the coset equality by `∼-congˡ`{.AgdaFunction}.

This encoding is chosen so that the library's congruence machinery applies to the
G-set verbatim: `cosetAlgebra`{.AgdaFunction} is an `Algebra`{.AgdaRecord} over
an ordinary signature, so `Con cosetAlgebra` means exactly what it means for any
algebra.  (The module ends with a private demonstration.)[^1]

We occasionally write `G ↷ G / H` to denote that the group G acts on the coset
space G / H, but we also use it to mean the algebra `cosetAlgebra`{.AgdaFunction}
that encodes this action; the context should make clear which is intended.

**Note on the symbol set**.  Operation symbols form a type with propositional
equality, so two setoid-equal but distinct carrier elements give two symbols; they
act identically on `G / H` (by `∼-congˡ` and `≈⇒∼`), and a signature is raw syntax,
so this is harmless.

The action laws are stated with the curried operations, which is no loss: by the
definition of `mkAlgebra`{.AgdaFunction}, the interpretation of the symbol `g` at
`x` is definitionally `g ∙ x`, so `act-identity`{.AgdaFunction} and
`act-compatible`{.AgdaFunction} are literally the unit and compatibility laws of
the group action `G ↷ G / H`, and `act-transitive`{.AgdaFunction} says the action
is transitive: any coset is reached from any other by some group element.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Group.GSet where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns  using ( 0F )
open import Data.Product       using ( _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Level              using ( Level ; _⊔_ ; suc )
open import Relation.Nullary   using ( Dec )
open import Relation.Unary     using ( Pred )

import Algebra.Properties.Group as GroupProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Bundles.Group               using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Unary            using ( Sig-Unary )
open import Classical.Structures.Group.Basic      using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup )
open import Classical.Structures.Group.Cosets     using ( module Coset )
open import Setoid.Congruences.Basic              using ( Con )
open import Setoid.Algebras.Basic                 using ( 𝕌[_]; Algebra ; mkAlgebra)
open import Setoid.Algebras.Finite                using ( FiniteAlgebra )
```
-->

#### The coset algebra

```agda
module CosetAction {α ρ : Level} (𝒢 : Group α ρ) {ℓ : Level}
  (H : Pred 𝕌[ proj₁ 𝒢 ] ℓ) (H-isSubgroup : IsSubgroup 𝒢 H)
  where

  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Group-Op 𝒢               using ( _∙_ ; ε ; _⁻¹ ; assoc-law ; idˡ-law )
  open Coset 𝒢 H H-isSubgroup   using ( _∼_ ; ∼-congˡ ; ≈⇒∼ ; cosetSetoid )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ  using ( //-rightDividesˡ )

  -- The algebra G ↷ G / H over the unary signature on the carrier of G:
  -- the symbol g acts on the coset of x by left translation, g ∙ x.

  cosetAlgebra : Algebra {𝑆 = Sig-Unary G} α ℓ
  cosetAlgebra = mkAlgebra cosetSetoid (λ g a → g ∙ a 0F) (λ g u∼v → ∼-congˡ g (u∼v 0F))
```

#### Action laws and transitivity

As explained above, the coset space is a `G`-set: `G` acts on `G / H` by left
translation.  The first two results we prove are the action laws; the third,
transitivity, is not an axiom but a further property this particular action
happens to have.  Each is a one-line consequence of a group law transported across
`≈⇒∼`{.AgdaFunction}.  (Recall, `≈⇒∼` says setoid equality refines coset equality:
`∀ {x y} → x ≈ y → x ∼ y`.)

+  `act-identity`{.AgdaFunction}: acting by `ε` does nothing, from
   `idˡ-law`{.AgdaFunction}.
+  `act-compatible`{.AgdaFunction}: acting by `g ∙ h` is acting by `h` and then by
   `g`, from `assoc-law`{.AgdaFunction}.
+  `act-transitive`{.AgdaFunction}: the action is transitive, and the witness is
   explicit: `y ∙ x ⁻¹` carries the coset of `x` to that of `y`.

Transitivity is the substantive one: it says `G / H` is a single orbit, which is
why a coset space is the model case of a transitive action.  Since it is proved by
exhibiting a witness, the group element, rather than by an existence argument, the
result it usable computationally.

```agda
  -- The identity element acts as the identity on cosets.
  act-identity : (x : G) → (ε ∙ x) ∼ x
  act-identity x = ≈⇒∼ (idˡ-law x)

  -- Acting by g ∙ h is acting by h, then by g.
  act-compatible : (g h x : G) → (g ∙ h) ∙ x ∼ g ∙ (h ∙ x)
  act-compatible g h x = ≈⇒∼ (assoc-law g h x)

  -- The action is transitive: y ∙ x ⁻¹ carries the coset of x to the coset of y.
  act-transitive : (x y : G) → Σ[ g ∈ G ] (g ∙ x) ∼ y
  act-transitive x y = y ∙ x ⁻¹ , ≈⇒∼ (//-rightDividesˡ x y)
```

Note that `_∙_` has higher precedence than `_∼_`, so we could have written
(ε ∙ x) ∼ x as `ε ∙ x ∼ x` without ambiguity.  Also, since `_∙_` is
left-associative, we could have written `g ∙ h ∙ x ∼ g ∙ (h ∙ x)` in
`act-compatible`{.AgdaFunction}.  We chose instead to make the laws readable even
without thinking about precedence conventions or associativity handedness.

#### Finiteness of the coset algebra

Carrier finiteness of the coset algebra is inherited from the group.  The coset
space is the *same* carrier under the coarser equality `_∼_`{.AgdaFunction}, so the
group's surjective enumeration still hits every element (the finer `_≈_`{.AgdaFunction}
refines `_∼_`{.AgdaFunction} by `≈⇒∼`{.AgdaFunction}), and decidable coset equality
is exactly the decidability of `_∼_`{.AgdaFunction}, which is supplied by
`∼-dec`{.AgdaFunction} of [Classical.Structures.Group.Cosets][] whenever membership
in `H`{.AgdaBound} is decidable.[^2]

```agda
  open FiniteAlgebra

  -- A finite group with decidable coset equality has a finite coset algebra.
  cosetAlgebra-FiniteAlgebra :
    FiniteAlgebra 𝑮 → (∀ x y → Dec (x ∼ y)) → FiniteAlgebra cosetAlgebra
  cosetAlgebra-FiniteAlgebra fin dec ._≟_         = dec
  cosetAlgebra-FiniteAlgebra fin dec .card        = fin .card
  cosetAlgebra-FiniteAlgebra fin dec .enum        = fin .enum
  cosetAlgebra-FiniteAlgebra fin dec .enum-sur x  =
    fin .enum-sur x .proj₁ , ≈⇒∼ (fin .enum-sur x .proj₂)
```

#### The congruence machinery applies verbatim

`cosetAlgebra` is an ordinary algebra, so its congruence lattice needs no new
definitions.  The demonstration below type-checks against the stock
`Con`{.AgdaFunction} of [Setoid.Congruences.Basic][].  We will eventually show
that this type is isomorphic (as a lattice) to the interval `[H, G]` in
`Sub(G)`.[^1]

```agda
  private
    _ : Type (α ⊔ suc ℓ)
    _ = Con cosetAlgebra ℓ
```

---

[^1]:  The `cosetAlgebra` algebra is the object of work package WP-3 of the FLRP
       program in which we prove `Con (G ↷ G / H) ≅ [H, G]`.
       (See `docs/notes/flrp-research-roadmap.md` § 7.)

[^2]:  This discharges, constructively, the finiteness hypothesis of the
       Pálfy–Pudlák corollaries of [FLRP.Bridge][].  (Audit A2 of
       `docs/notes/flrp-wp7-audits.md` sketches precisely this argument.)
