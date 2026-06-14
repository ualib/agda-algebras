---
layout: default
file: "src/Classical/Structures/Semigroup.lagda.md"
title: "Classical.Structures.Semigroup module"
date: "2026-05-18"
author: "the agda-algebras development team"
---

### Semigroups — the first equation-bearing classical structure

This is the [Classical.Structures.Semigroup][] module of the [Agda Universal Algebra Library][].

A *semigroup* is a magma whose binary operation is associative.  Type-theoretically,
this is the Σ-typed structure consisting of an `Sig-Magma`-algebra `𝑨` paired with a
proof that `𝑨` satisfies `Th-Semigroup`.  Mathematically: a semigroup *is* an
algebra equipped with a proof that it satisfies the semigroup theory.  The Σ encodes
that reading directly, per
[ADR-002 v2 §5](../../docs/adr/002-classical-layer-design.md).

This is the first concrete classical structure with a non-empty equational theory,
and consequently this module's prose is normative for every subsequent
equation-bearing structure (Monoid, Group, Lattice, Ring).
Specifically, the conventions documented and embodied here are as follows.

+  **Theory representation**.  Each equation-bearing structure `X` has a
   `Classical/Theories/X.lagda.md` file housing a singleton-or-larger index enum
   `Eq-X` and a theory function `Th-X : Eq-X → Term (Fin n) × Term (Fin n)` composed
   from generic equation builders in [`Classical.Equations`][].  The Σ-typed core
   `X α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-X` lives in `Classical/Structures/X.lagda.md`
   over `open Setoid.Algebras {𝑆 = Sig-X}`.
+  **`_⊨_` alias**.  Each structure file defines a local `_⊨_` with the codomain
   *spelled out explicitly* — for Semigroup, `Eq-Semigroup → Term (Fin 3) × Term (Fin 3)`,
   not `_`.  (The underscore lets Agda's unifier wander into the equational-logic
   substrate, where it produces error messages naming `Modᵗ` rather than the local
   alias.) The alias's body unfolds `Modᵗ Th-X` once at the point of use.
+  **Named accessor module `<Structure>-Op`**.  The signature-mechanics convention
   — one named parametric module per structure exposing curried,
   infix-friendly accessors so that downstream code can `open <Structure>-Op 𝑿` once
   and write `a ∙ b` thereafter — extends to equation-bearing structures by additively
   re-exporting the predecessor's accessors through the forgetful projection and by
   adding new accessors for the equation-witness proofs.  Concretely, `Semigroup-Op 𝑺`
   exposes `_∙_` inherited from `Magma-Op (semigroup→magma 𝑺)` via
   `open Magma-Op (semigroup→magma 𝑺) public using (_∙_)`, plus the new
   `equations : (semigroup→magma 𝑺) ⊨ Th-Semigroup` accessor projecting the
   satisfaction-witness, and the curried-form laws derived from it — for Semigroup,
   `assoc-law : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)`.  The laws are stated in the
   curried form working algebraists use, so that the bundle bridge's law-fields and
   any downstream consumer get them as one-liners rather than re-deriving them from
   `equations`.  The single point where the Fin 2 η-gap between term-interpretation
   form and curried form is paid is the local `interp-node` lemma, contained here so
   that neither the bundle bridge nor any consumer touches it.  Subsequent
   `Monoid-Op`, `Group-Op`, `Lattice-Op`, `Ring-Op` follow the same template —
   each exposes its predecessor's laws (inherited through the forgetful) plus its
   own new laws in curried form.  Note that `Domain` and `Carrier` are *not* re-exposed
   via the named module; they remain accessible through the foundation's
   blackboard-bold accessors `𝔻[ semigroup→magma 𝑺 ]` and `𝕌[ semigroup→magma 𝑺 ]`,
   which avoid potential clashes with field names of the same provenance in stdlib
   bundle records.
+  **Forgetful projection `<structure>→<weaker>`**.  Each equation-bearing structure
   `X` ships a forgetful function `x→y : X α ρ → Y α ρ` to its immediate predecessor
   `Y` in the hierarchy.  When `Y`'s underlying signature is the same as `X`'s
   (i.e., `X` adds equations only — no new operation symbols), the forgetful is
   simply `proj₁`.  When `X` adds operation symbols on top of `Y`'s signature, the
   forgetful is more substantial (it projects out the additional operations); those
   cases land with Monoid.  For Semigroup over Magma there are no added
   symbols, so `semigroup→magma = proj₁`.  Composition of forgetfuls down the
   hierarchy expresses inheritance type-theoretically: a group `𝑮` is a monoid via
   `group→monoid 𝑮`, a semigroup via `monoid→semigroup ∘ group→monoid`, and a magma
   via `semigroup→magma ∘ monoid→semigroup ∘ group→monoid`.
+  **`eqsTo`-family constructor factoring through the predecessor's `opsTo`-family**.
   The user-facing constructor `eqsToSemigroup` builds a semigroup from a bare type `A`,
   a binary operation `_·_ : A → A → A`, and one propositional-equality proof per
   equation in the theory (here, one `·-assoc` proof).  Its definition factors
   through `opsToMagma`: `eqsToSemigroup A _·_ ·-assoc = opsToMagma A _·_ , <proof>`,
   reusing the underlying-algebra construction rather than rebuilding it.
   This factoring has two payoffs: it keeps the per-structure constructor short, and
   it makes the forgetful acceptance criterion `semigroup→magma (eqsToSemigroup A _·_ _)
   ≡ opsToMagma A _·_` discharge by `refl`.  Subsequent `eqsTo`-family constructors
   (for Monoid, Group, Lattice, Ring) follow the same shape, each factoring
   through their immediate predecessor's concrete constructor family.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Classical.Structures.Semigroup where

open import Agda.Primitive                          using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -------------------------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ ; suc )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  as ≡ using ( _≡_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Func renaming ( to to _⟨$⟩_ )

-- Imports from the Agda Universal Algebra Library -----------------------------------------------
open import Classical.Operations                   using ( pair )
open import Classical.Signatures.Magma             using ( Sig-Magma ; ∙-Op )
open import Classical.Structures.Magma             using ( Magma ; opsToMagma ; module Magma-Op )
open import Classical.Theories.Semigroup           using ( Eq-Semigroup ; Th-Semigroup ; assoc )
open import Overture.Terms {𝑆 = Sig-Magma}         using ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic {𝑆 = Sig-Magma}  using ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Terms {𝑆 = Sig-Magma}           using ( module Environment )
open import Setoid.Varieties.EquationalLogic {𝑆 = Sig-Magma} using ( _⊧_≈_ )

open Algebra using ( Interp )

private variable α ρ : Level
```

#### The local satisfaction predicate

`𝑨 ⊨ ℰ` says that the algebra `𝑨` satisfies every equation in the theory `ℰ` — that
is, for every equation `(p , q) = ℰ i`, the formulas `p` and `q` evaluate to setoid-equal
elements under every environment.  This is `Modᵗ ℰ 𝑨` from
[`Setoid.Varieties.EquationalLogic`][], unfolded once to bring the codomain
type-shape into view at the use site.

```agda
infix 4 _⊨_
_⊨_ : (𝑨 : Algebra α ρ) (ℰ : Eq-Semigroup → Term (Fin 3) × Term (Fin 3)) → Type (α ⊔ ρ)
𝑨 ⊨ ℰ = ∀ i → 𝑨 ⊧ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
```

#### The type of semigroups

```agda
Semigroup : (α ρ : Level) → Type (suc α ⊔ suc ρ)
Semigroup α ρ = Σ[ 𝑨 ∈ Algebra α ρ ] 𝑨 ⊨ Th-Semigroup
```

#### The forgetful projection to magmas

A semigroup is a magma + a proof that its operation is associative; forgetting the
proof recovers the magma.

```agda
semigroup→magma : Semigroup α ρ → Magma α ρ
semigroup→magma = proj₁
```

#### The `Semigroup-Op` module: named accessors for a fixed semigroup

`Semigroup-Op 𝑺` exposes `_∙_` (re-exported from `Magma-Op (semigroup→magma 𝑺)`
through the forgetful) and `equations` (the satisfaction-witness proof, projected
out of the Σ).  Users `open Semigroup-Op 𝑺` at a use site to bring both into scope;
the binary operation is then available in infix form `a ∙ b`, mirroring the
`open Semigroup S`-and-then-`a ∙ b` idiom of `Algebra.Bundles`.

The pattern — *each `<Structure>-Op` module re-exports its immediate predecessor's
`<Weaker>-Op` accessors through the forgetful projection, then adds new accessors
for the equation-witness proofs* — is the normative inheritance idiom for the whole
hierarchy.

```agda
module Semigroup-Op {α ρ : Level} (𝑺 : Semigroup α ρ) where
  open Magma-Op (semigroup→magma 𝑺) public using ( _∙_ )

  equations : semigroup→magma 𝑺 ⊨ Th-Semigroup
  equations = proj₂ 𝑺

  private
    𝑴 = semigroup→magma 𝑺
  open Setoid 𝔻[ 𝑴 ]
  open Environment 𝑴 using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑴 ]
  -- Binary congruence of the interpreted operation.  This is the same content as
  -- the stdlib `isMagma.∙-cong` field; naming it here lets both that field (in the
  -- bundle bridge) and `assoc-law` below reuse it as a reasoning step.
  ∙-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x ∙ u) ≈ (y ∙ v)
  ∙-cong x≈y u≈v = cong (Interp 𝑴) (≡.refl , λ { 0F → x≈y ; 1F → u≈v })

  -- The Fin 2 η-containment lemma — the single point in the whole Semigroup layer where
  -- the cost of the gap between term-interpretation form and curried form is paid.
  --   LHS reduces to  Interp 𝑴 ⟨$⟩ (∙-Op , λ i → ⟦ pair s t i ⟧ ⟨$⟩ η)
  --   RHS reduces to  Interp 𝑴 ⟨$⟩ (∙-Op , pair (⟦ s ⟧ ⟨$⟩ η) (⟦ t ⟧ ⟨$⟩ η))
  -- The two argument tuples agree at 0F and 1F but not definitionally (no η on
  -- `Fin 2 → A`), so `cong (Interp 𝑴)` bridges them pointwise.  In the 4.0 cubical
  -- port this lemma becomes `funExt (λ { 0F → refl ; 1F → refl })`; the content is
  -- identical and the definitional gap is unchanged, so containing it in this one
  -- named lemma is what makes the port mechanical.
  interp-node : (s t : Term (Fin 3)) (η : Fin 3 → 𝕌[ 𝑴 ])
              → ⟦ node ∙-Op (pair s t) ⟧ ⟨$⟩ η ≈ (⟦ s ⟧ ⟨$⟩ η) ∙ (⟦ t ⟧ ⟨$⟩ η)
  interp-node s t η = cong (Interp 𝑴) (≡.refl , λ { 0F → refl ; 1F → refl })

  -- Associativity in curried form.  The `equations assoc η` step is the actual
  -- mathematical content (associativity in term-interpretation form); the four
  -- surrounding steps reassociate `interp-node` and `∙-cong` to carry it between
  -- the curried endpoints.  This is the law in the form working algebraists want,
  -- and it is what the bundle bridge's `assoc` field reduces to.
  assoc-law : ∀ x y z → x ∙ y ∙ z ≈ x ∙ (y ∙ z)
  assoc-law x y z = begin
    (x ∙ y) ∙ z          ≈⟨ ∙-cong (sym (interp-node (ℊ 0F) (ℊ 1F) η)) refl ⟩
    (⟦ Lt ⟧ ⟨$⟩ η) ∙ z   ≈⟨ sym (interp-node Lt (ℊ 2F) η) ⟩
    ⟦ lhsT ⟧ ⟨$⟩ η       ≈⟨ equations assoc η ⟩
    ⟦ rhsT ⟧ ⟨$⟩ η       ≈⟨ interp-node (ℊ 0F) Rt η ⟩
    x ∙ (⟦ Rt ⟧ ⟨$⟩ η)   ≈⟨ ∙-cong refl (interp-node (ℊ 1F) (ℊ 2F) η) ⟩
    x ∙ (y ∙ z)          ∎
    where
    η : Fin 3 → 𝕌[ 𝑴 ]
    η = λ { 0F → x ; 1F → y ; 2F → z }
    Lt   = node ∙-Op (pair (ℊ 0F) (ℊ 1F))
    Rt   = node ∙-Op (pair (ℊ 1F) (ℊ 2F))
    lhsT = node ∙-Op (pair Lt (ℊ 2F))
    rhsT = node ∙-Op (pair (ℊ 0F) Rt)
```

#### `eqsToSemigroup`

This is the canonical constructor for downstream users.  Given a carrier
type `A`, a binary operation `_·_ : A → A → A`, and a propositional-equality
associativity proof `·-assoc`, it returns a `Semigroup α α`.  The construction
factors through `opsToMagma` so that the underlying-algebra portion is shared with
the `Magma` constructor — this is what makes the forgetful agreement criterion
`semigroup→magma ∘ eqsToSemigroup A _·_ _ ≡ opsToMagma A _·_` discharge by
`refl`.

The associativity proof discharges by direct evaluation: under `≡.setoid A`, the
setoid equivalence is propositional equality; the interpretation of
`(ℊ 0F ∙ ℊ 1F) ∙ ℊ 2F` in `opsToMagma A _·_` under an environment `ρ` reduces
definitionally to `(ρ 0F · ρ 1F) · ρ 2F`, and the mirror reduction holds for the
right-associated term, so `·-assoc (ρ 0F) (ρ 1F) (ρ 2F)` is exactly the proof
required.

```agda
eqsToSemigroup : (A : Type α) (_·_ : A → A → A)
  (·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)) → Semigroup α α

eqsToSemigroup A _·_ ·-assoc = opsToMagma A _·_ , proof
  where
  proof : opsToMagma A _·_ ⊨ Th-Semigroup
  proof assoc ρ = ·-assoc (ρ 0F) (ρ 1F) (ρ 2F)
```

--------------------------------------

<span style="float:left;">[← Classical.Structures.Magma](Classical.Structures.Magma.html)</span>
<span style="float:right;">[Classical.Structures.Monoid →](Classical.Structures.Monoid.html)</span>

{% include UALib.Links.md %}
