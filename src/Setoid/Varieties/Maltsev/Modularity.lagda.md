---
layout: default
file: "src/Setoid/Varieties/Maltsev/Modularity.lagda.md"
title: "Setoid.Varieties.Maltsev.Modularity module (The Agda Universal Algebra Library)"
date: "2026-06-19"
author: "the agda-algebras development team"
---

### Maltsev conditions: congruence modularity

This is the [Setoid.Varieties.Maltsev.Modularity][] module of the [Agda Universal Algebra Library][].

This module records the encoding congruence modularity (CM) — the Day identities, as
a theory interpretation `Th-Day n ≼ ℰ` — and states Day's theorem.

#### Modularity of the congruence lattice

CM is a properties of the congruence *lattice*, defined in
[Setoid.Congruences.Properties][] as `CongruenceModular` (at the absorbing relation
level, so that meet and join are operations on a single type).  We it here to
phrase the Day variety condition below.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Varieties.Maltsev.Modularity where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ----------------------------
open import Data.Bool.Base                     using  ( if_then_else_ )
open import Data.Fin.Base                      using  ( Fin ; toℕ ; fromℕ ; inject₁ )
                                               renaming ( zero to fzero ; suc to fsuc )
open import Data.Fin.Patterns                  using  ( 0F ; 1F ; 2F ; 3F )
open import Data.Nat.Base                      using  ( ℕ ; suc )
open import Data.Product                       using  ( _×_ ; _,_ ; Σ-syntax )
open import Level                              using  ( Level ; 0ℓ ; _⊔_ )
                                               renaming ( suc to lsuc )
open import Relation.Binary                    using  ( Setoid )

-- -- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture.Basic                     using  ( _⇔_ )
open import Overture.Signatures                using  ( Signature )
open import Overture.Terms                     using  ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Properties      using  ( CongruenceModular )
open import Setoid.Terms.Basic                 using  ( _[_] )
open import Setoid.Varieties.Interpretation    using  ( _⊨ₑ_ ; module Interpret )
open import Setoid.Varieties.Maltsev.Basic     using  ( even? )

open import Function using ( Func )

private variable α ρ χ ι ℓ : Level
```


#### Day terms (congruence modularity)

Congruence modularity is characterized by a chain of *quaternary* terms `m₀ , … , mₙ`,
the **Day terms**[^day] (Day 1969; Burris–Sankappanavar, Thm. 12.4), with identities

    m₀(x,y,z,u) ≈ x,   mₙ(x,y,z,u) ≈ u,   mᵢ(x,y,y,x) ≈ x   (all i),
    mᵢ(x,x,u,u) ≈ mᵢ₊₁(x,x,u,u)  (i even),  mᵢ(x,y,y,u) ≈ mᵢ₊₁(x,y,y,u)  (i odd).

```agda
-- the canonical 4-element tuple over the variable carrier Fin 4
quad : {ℓ : Level}{A : Type ℓ} → A → A → A → A → Fin 4 → A
quad a b c d 0F = a
quad a b c d 1F = b
quad a b c d 2F = c
quad a b c d 3F = d

module _ (n : ℕ) where

  -- n+1 quaternary operation symbols.
  Sig-Day : Signature 0ℓ 0ℓ
  Sig-Day = Fin (suc n) , (λ _ → Fin 4)

  private
    d : Fin (suc n) → (a b c d : Term (Fin 4)) → Term (Fin 4)
    d i a b c d = node i (quad a b c d)

    x y z u : Term {𝑆 = Sig-Day} (Fin 4)
    x = ℊ 0F ; y = ℊ 1F ; z = ℊ 2F ; u = ℊ 3F

  data Eq-Day : Type where
    mxyzu≈x  : Eq-Day                 -- m₀(x,y,z,u) ≈ x
    mxyyx≈x  : Fin (suc n) → Eq-Day   -- mᵢ(x,y,y,x) ≈ x
    mxyzu≈u  : Eq-Day                 -- mₙ(x,y,z,u) ≈ u
    m-fork   : Fin n → Eq-Day         -- consecutive mᵢ, mᵢ₊₁ agree (parity-dependent)

  Th-Day : Eq-Day → Term (Fin 4) × Term (Fin 4)
  Th-Day mxyzu≈x      = d fzero x y z u , x
  Th-Day mxyzu≈u      = d (fromℕ n) x y z u , u
  Th-Day (mxyyx≈x i)  = d i x y y x , x
  Th-Day (m-fork i)   = if even? (toℕ i)
    then ( d (inject₁ i) x x u u , d (fsuc i) x x u u )   -- i even: agree on (x,x,u,u)
    else ( d (inject₁ i) x y y u , d (fsuc i) x y y u )   -- i odd:  agree on (x,y,y,u)

HasDayTerms : (n : ℕ)(α ρ : Level){𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
  → (Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) → Type (lsuc (α ⊔ ρ) ⊔ χ ⊔ ι)
HasDayTerms n α ρ ℰ = Th-Day n ≼ ℰ
  where open Interpret α ρ
```

The curried extraction for the Day chain is the verbatim quaternary analogue of the Jónsson
`d𝑩`{.AgdaFunction} / `eval-d`{.AgdaFunction} block (over `quad`{.AgdaFunction} in place of
`tri`{.AgdaFunction}).  The forward **staircase**, however, is *not* a mechanical mirror of
Jónsson's, and is deferred.  The reason is structural: the ψ-pinning that makes Jónsson's
argument go through — every `dᵢ(a,·,b)` is θ-tied to `a` via `dᵢ(x,y,x) ≈ x` — needs, for the
Day term `mᵢ(x,y,y,x) ≈ x`, the **two** middle arguments to be *equal*, so only elements
`mᵢ(a,c,c,b)` are ψ-pinnable.  The even-fork column `mᵢ(a,a,b,b)` (middles `a , b`, unequal) is
therefore *not* pinnable, and connecting it to the pinnable columns demands a single-slot
`a ↔ b` move that is not a `θ∨(φ∧ψ)`-step.  Jónsson's two-column staircase has no analogue
here; Day's theorem needs the genuinely different (2-dimensional / `A²`) construction of Day
1969, recorded for a successor in the design note `docs/notes/m6-6-forward-jonsson-day.md`.

#### The conditions as properties of a variety, and the deferred theorems

Fix a theory `ℰ` and the level pair `(α , ρ)` at which models are tested.
A *congruence-modular variety* is one in which all models are
congruence-modular (CM).  The Day characterizations of CM varieties is the iff statement
`Day-Statement`{.AgdaFunction}.  The **forward** (term ⟹ CM) half —
`day⇒CongruenceModularity`{.AgdaFunction} below — and the reverse (CM ⟹ terms) are deferred
for a substantive reason recorded above and in the design note, not mere lack of effort.

```agda
module _ {α ρ ℓ : Level}{𝑆 : Signature 0ℓ 0ℓ}{X : Type χ}{Idx : Type ι}
         (ℰ : Idx → Term {𝑆 = 𝑆} X × Term {𝑆 = 𝑆} X) where

  -- Every model is congruence-modular.
  CongruenceModularVariety : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  CongruenceModularVariety = (𝑩 : Algebra α ρ) → 𝑩 ⊨ₑ ℰ → CongruenceModular 𝑩 ℓ

  -- Day's theorem: CM ⇔ existence of Day terms.  Unlike Jónsson, the
  -- forward staircase is *not* a mechanical mirror — see the design note
  -- `docs/notes/m6-6-forward-jonsson-day.md`.
  Day-Statement : Type (χ ⊔ ι ⊔ lsuc (α ⊔ ρ ⊔ ℓ))
  Day-Statement = CongruenceModularVariety ⇔ ( Σ[ n ∈ ℕ ] HasDayTerms n α ρ ℰ )
```

---

[^day]: A. Day, *A characterization of modularity for congruence lattices of algebras*, Canad. Math. Bull. **12** (1969), 167–173.  [doi:10.4153/CMB-1969-016-6](https://doi.org/10.4153/CMB-1969-016-6).
