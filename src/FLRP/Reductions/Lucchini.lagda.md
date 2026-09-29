---
layout: default
file: "src/FLRP/Reductions/Lucchini.lagda.md"
title: "FLRP.Reductions.Lucchini module (The Agda Universal Algebra Library)"
date: "2026-09-28"
author: "the agda-algebras development team"
---

### Entry 14: Lucchini's dichotomy for minimal representations of `Mₙ`

This is the [FLRP.Reductions.Lucchini][] module of the [Agda Universal Algebra Library][].

The lattices `Mₙ` of height two are the classical stress test of the
representation problem, and the literature on them is a reduction program of
its own, older than Aschbacher's and the model for it.  Köhler [1983] showed
that a group of least order with an `Mₙ` interval, `n − 1` not a prime power,
has a unique minimal normal subgroup, which is nonabelian (Entry 6 of
[FLRP.Reductions][]).  Lucchini (1994)[^1] then proved the dichotomy this
module records: for `n` large enough, such a group is almost simple, or the
representing subgroup meets the socle trivially, unless `n` lies in one of
the two families he had already shown to be representable.  Baddeley and
Lucchini (1997)[^2] take the second alternative apart into a tree of
questions about finite simple groups (their "results diagram"); the survey
note `docs/notes/flrp-m6-27-paths.md` § 4 records that tree in prose, since
its vocabulary (twisted wreath products, sections of simple groups, and the
tuples that encode them) is beyond what the library can state.  What the
library can state is the dichotomy itself, and this module does.

**The theorem** (Lucchini 1994, read in the published text).  Let `n − 1` not
be a prime power and let `G` be a finite group of least order among those
with a subgroup `H` such that `[H, G] ≅ Mₙ`.  If `n` is large enough (the
paper says "for example `n ≥ 50`") then one of the following holds: `G` is
almost simple; `H ∩ Soc(G) = 1`; `n = q + 2` for a prime power `q`; or
`n = (qᵗ + 1)/(q + 1) + 1` for a prime power `q` and an odd prime `t`.

**Why it belongs beside Entry 13**.  Lucchini's first reduction (his 1.1
through 1.8) is the `Mₙ` prototype of the arguments Aschbacher's Section 4
runs for D-lattices, and of the ones Entry 13 runs for parachutes: the
interval is presented inside the socle as its `H`-invariant subgroups (his
1.3); if `H ∩ Soc(G)` projects onto a component then the interval is the dual
of an interval in `H`, a smaller group (his 1.4, Aschbacher's (4.13)); if
every maximal `H`-invariant subgroup is of product type then the interval
lives in `N_G(T)/C_G(T)`, a smaller group (his 1.6, Aschbacher's (4.12)(7)
and (6.5)); and the components may be taken to be one orbit block (his 1.8).
`Mₙ` is self-dual and coatomistic, which is why both the dual step and the
product-type step go through without a caveat there.

**What is imported and what is derived**.  The dichotomy is imported as the
named hypothesis `LucchiniDichotomy`{.AgdaFunction}, over the vocabulary of
Entry 13 (`Minimal`{.AgdaFunction} for the minimality, and the almost simple
alternative `MonolithSimple`{.AgdaFunction}) with the monolith supplied as
an argument, exactly as Köhler's theorem (Entry 6) produces it; the
composition of the two entries is derived
(`lucchini-with-kohler`{.AgdaFunction}).  The two arithmetic families are
stated over the standard library's primes: `n = q + 2` as "`n − 2` is a prime
power", and `n = (qᵗ + 1)/(q + 1) + 1` as `(n − 1)(q + 1) = qᵗ + 1`, which
avoids division.  The bound `50 ≤ n` is the paper's example bound, taken as
the hypothesis; the paper's "large enough" is not a sharper statement.

**Representability status**.  `Mₙ` is group representable for every `n` in
Lucchini's set `K` (`n = 1, 2, q + 1, q + 2, (qᵗ + 1)/(q + 1) + 1`), so the
entry is non-vacuous on that set; for `n ∉ K` it is the open question, and
the smallest such `n` is `16`, which lies *below* the bound and so outside
the entry: for `16 ≤ n ≤ 50` the third alternative of Baddeley–Lucchini's
(2.F), a non-simple socle meeting `H` nontrivially, is not excluded by
anything in the two papers.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Reductions.Lucchini where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Nat.Base                          using  ( ℕ ; _+_ ; _*_ ; _∸_ ; _^_ )
                                                   renaming ( _≤_ to _≤ⁿ_ )
open import Data.Nat.Primality                     using  ( Prime )
open import Data.Product                           using  ( _×_ ; Σ-syntax ; proj₁ )
open import Data.Sum.Base                          using  ( _⊎_ )
open import Level                                  using  ( 0ℓ )
                                                   renaming ( suc to lsuc )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ )
open import Relation.Nullary                       using  ( ¬_ )
open import Relation.Unary                         using  ( Pred ; _⊆_ ; _∩_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group              using  ( Group ; IsSubgroup
                                                           ; module MinimalNormal )
open import FLRP.Enforceable                        using  ( IntervalIso )
open import FLRP.Reductions                         using  ( M[_] ; module Entry-Minimal )
open import FLRP.Reductions.Coatomistic             using  ( Minimal ; module Alternatives )
open import Setoid.Algebras                         using  ( 𝕌[_] ; FiniteAlgebra )
```
-->

#### The arithmetic side

A prime power, and the two families Lucchini had shown representable.

```agda
-- q is a prime power: q = pᵏ for a prime p and k ≥ 1.
IsPrimePower : ℕ → Type
IsPrimePower q = Σ[ p ∈ ℕ ] Σ[ k ∈ ℕ ] ( Prime p × 1 ≤ⁿ k × q ≡ p ^ k )

-- An odd prime: a prime of the form 2s + 1.
IsOddPrime : ℕ → Type
IsOddPrime t = Prime t × Σ[ s ∈ ℕ ] t ≡ 1 + 2 * s

-- Lucchini's two representable families: n = q + 2, or
-- n = (qᵗ + 1)/(q + 1) + 1, the latter written without division.
InLucchiniFamilies : ℕ → Type
InLucchiniFamilies n =
    IsPrimePower (n ∸ 2)
  ⊎ Σ[ q ∈ ℕ ] Σ[ t ∈ ℕ ] ( IsPrimePower q × IsOddPrime t × ((n ∸ 1) * (q + 1) ≡ q ^ t + 1) )
```

#### Entry 14, imported

**Property**.  A statement about the pair `(H , G)` and the integer `n`: `G`
is almost simple, or `H` meets the monolith trivially, or `n` lies in one of
the two families.

**Enforcing lattice**.  `Mₙ`, for `n ≥ 50` with `n − 1` not a prime power.

**Source**.  Lucchini [1994], the Theorem of its introduction, read in the
published text (a scan; the statement page was read as an image).

**Level**.  Minimal representations only (`Minimal`{.AgdaFunction}, over
representations of `Mₙ`, which is self-dual, so the dual-closed and the plain
minimality coincide); the theorem is about finite groups, so finiteness is
the `FiniteAlgebra`{.AgdaRecord} antecedent the minimality carries.

```agda
-- Entry 14: Lucchini's dichotomy, for a minimal representation of Mₙ with
-- n ≥ 50 and n − 1 not a prime power, given the monolith of the group.
LucchiniDichotomy : Type (lsuc 0ℓ)
LucchiniDichotomy =
  ∀ (n : ℕ) → 50 ≤ⁿ n → ¬ IsPrimePower (n ∸ 1)
  → ∀ (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → (fin : FiniteAlgebra (proj₁ 𝒢)) → IntervalIso 𝒢 H H-sg M[ n ]
  → Minimal 𝒢 fin M[ n ]
  → (mono : MinimalNormal.HasMonolithᵍ 𝒢 0ℓ)
  →   Alternatives.MonolithSimple 𝒢 H mono
    ⊎ ((H ∩ proj₁ mono) ⊆ MinimalNormal.Triv 𝒢 0ℓ)
    ⊎ InLucchiniFamilies n
```

#### Composition with Köhler's theorem

Entry 6 imports Köhler's theorem as `Kohler n`, minimal enforceability of the
class `𝒢₂` (a monolith exists) via `Mₙ`; it supplies exactly the monolith the
dichotomy asks for, so the two imports compose into a statement with no
monolith argument.  The minimality hypothesis of `MinimallyIE`{.AgdaFunction}
is `Minimal`{.AgdaFunction} spelled out, so it is passed through unchanged.

```agda
-- Köhler's monolith fed to Lucchini's dichotomy.
lucchini-with-kohler : LucchiniDichotomy
  → ∀ (n : ℕ) (kohler : Entry-Minimal.Kohler n) → 50 ≤ⁿ n → ¬ IsPrimePower (n ∸ 1)
  → ∀ (𝒢 : Group 0ℓ 0ℓ) (H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ) (H-sg : IsSubgroup 𝒢 H)
  → (fin : FiniteAlgebra (proj₁ 𝒢)) (iso : IntervalIso 𝒢 H H-sg M[ n ])
  → (least : Minimal 𝒢 fin M[ n ])
  →   Alternatives.MonolithSimple 𝒢 H (kohler 𝒢 H H-sg fin iso least)
    ⊎ ((H ∩ proj₁ (kohler 𝒢 H H-sg fin iso least)) ⊆ MinimalNormal.Triv 𝒢 0ℓ)
    ⊎ InLucchiniFamilies n
lucchini-with-kohler dich n kohler big notpp 𝒢 H H-sg fin iso least =
  dich n big notpp 𝒢 H H-sg fin iso least (kohler 𝒢 H H-sg fin iso least)
```

---

[^1]: A. Lucchini, *Intervals in subgroup lattices of finite groups*, Comm.
      Algebra 22 (1994), 529–549.  The Theorem is on p. 530; its first
      reduction (1.1 through 1.8) is on pp. 530–533.

[^2]: R. Baddeley and A. Lucchini, *On representing finite lattices as
      intervals in subgroup lattices of finite groups*, J. Algebra 196 (1997),
      1–100.  Its (2.F) records the union the dichotomy produces, and its
      Section 8 the four problems the reduction ends in.
