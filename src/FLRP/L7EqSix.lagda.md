---
layout: default
file: "src/FLRP/L7EqSix.lagda.md"
title: "FLRP.L7EqSix module (The Agda Universal Algebra Library)"
date: "2026-07-22"
author: "the agda-algebras development team"
---

### The Eq(6) sublattice witness for `L7`

This is the [FLRP.L7EqSix][] module of the [Agda Universal Algebra Library][].

By the Pudlák–Tůma theorem every finite lattice embeds into the lattice
`Eq(X)`{.AgdaFunction} of equivalence relations on some finite set `X`.  This module
formalizes the explicit witness for the distinguished open instance of the FLRP
program: `L7`{.AgdaFunction} — the seven-element lattice of
[Examples.Classical.Lattices.L7][], called `L10` in the DeMeo–Freese–Jipsen
manuscript *Representing Finite Lattices as Congruence Lattices of Finite
Algebras* — embeds into `Eq(6)`, the equivalence relations on a six-element set.

The witness and its provenance are recorded in the session note
[`docs/notes/flrp-l7-eq6.md`](docs/notes/flrp-l7-eq6.md) (issue #484): seven
partitions of `{0, …, 5}`, one per element of `L7`, closed under the meet and join
of `Eq(6)` in the pattern of the `L7` Cayley tables.  Six is the minimum possible
base set — `Eq(4)` and `Eq(5)` contain no copy of `L7` — but that census fact is
exhaustive-search material and stays in the note; this module formalizes the
*positive* content:

+  the seven partitions, as normal-form parent vectors in the sense of
   [Setoid.Congruences.Certificates.Schema][];
+  each induces an equivalence relation `_∼[ k ]_`{.AgdaFunction} on `Fin 6` (the
   kernel of its root lookup), and the assignment is injective;
+  **meets**: the relation of `k ∧ l` is the intersection of the relations of `k`
   and `l` — the meet of `Eq(6)`;
+  **joins**: the relation of `k ∨ l` contains both arguments' relations and is
   contained in *every* equivalence relation containing them — so it is the least
   upper bound in `Eq(6)`, the transitive closure of the union.

Meets, containments, injectivity, and normal form are all decided over the finite
carrier, exactly as in [Examples.Classical.Lattices.L7][]: a wrong table entry or a
wrong partition would make some decision compute to `no`{.AgdaInductiveConstructor}
and break compilation.  The join least-ness is the one genuinely quantified
statement (it ranges over arbitrary equivalence relations at any universe level);
it follows from a small generic lemma about bounded alternating chains plus one
decided fact — every point reaches its block root in the join partition by a chain
of at most four hops through the two argument partitions.

The lattice operations `_∧_`{.AgdaFunction} and `_∨_`{.AgdaFunction} are imported
from [Examples.Classical.Lattices.L7][], so the tables have a single source of
truth, and the element numbering is that module's: `0 = ⊥`, `1 = (1,0)`,
`2 = (0,1)`, `3 = x`, `4 = (1,1)`, `5 = (0,2)`, `6 = ⊤`.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.L7EqSix where

open import Agda.Primitive using ( Level ) renaming ( Set to Type )

-- Imports from Agda and the Agda Standard Library -----------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F ; 6F )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; any? )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product                           using ( _×_ ; _,_ ; Σ-syntax )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Vec.Base                          using ( _∷_ ; [] )
open import Data.Vec.Properties                    using ( ≡-dec )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; subst )
open import Relation.Nullary.Decidable.Core        using ( Dec ; _×-dec_ ; _⊎-dec_ ; _→-dec_ )

-- Imports from the Agda Universal Algebra Library -----------------------------
open import Overture.Cayley                        using ( from-yes )
open import Setoid.Congruences.Certificates.Schema using ( ParentVec ; parent
                                                         ; NormalForm ; normalForm? )
open import Examples.Classical.Lattices.L7         using ( _∧_ ; _∨_ )
```
-->

#### The seven partitions

Each element of `L7` is assigned a partition of `{0, …, 5}`, stored as a parent
vector in Freese normal form (every index points directly at the least element of
its block).  In bar notation, with singletons suppressed:

```text
θ 0F  =  Δ (the diagonal)          θ 4F  =  |0,1,2|3,4,5|
θ 1F  =  |0,2|3,4|                 θ 5F  =  |0,1|2,3|4,5|
θ 2F  =  |0,1|4,5|                 θ 6F  =  ∇ (one block)
θ 3F  =  |0,4|1,3|2,5|
```

```agda
-- The Eq(6) witness: one partition of Fin 6 per element of L7.
θ : Fin 7 → ParentVec 6
θ 0F = 0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ []
θ 1F = 0F ∷ 1F ∷ 0F ∷ 3F ∷ 3F ∷ 5F ∷ []
θ 2F = 0F ∷ 0F ∷ 2F ∷ 3F ∷ 4F ∷ 4F ∷ []
θ 3F = 0F ∷ 1F ∷ 2F ∷ 1F ∷ 0F ∷ 2F ∷ []
θ 4F = 0F ∷ 0F ∷ 0F ∷ 3F ∷ 3F ∷ 3F ∷ []
θ 5F = 0F ∷ 0F ∷ 2F ∷ 2F ∷ 4F ∷ 4F ∷ []
θ 6F = 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ []
```

Every vector is in Freese normal form, so equal partitions are equal vectors and
distinct vectors are distinct partitions; both facts below are decided by a sweep
over the finite carrier.

```agda
-- Each of the seven vectors is idempotent and decreasing (Freese normal form).
θ-normalForm : ∀ k → NormalForm (θ k)
θ-normalForm = from-yes (all? λ k → normalForm? (θ k))

-- The assignment is injective: distinct L7 elements get distinct partitions.
θ-injective : ∀ k l → θ k ≡ θ l → k ≡ l
θ-injective = from-yes (all? λ k → all? λ l → ≡-dec _≟_ (θ k) (θ l) →-dec (k ≟ l))
```

#### The induced equivalence relations

Two points are related by the `k`-th partition exactly when their roots agree.
This is the kernel of the root lookup, so reflexivity, symmetry, and transitivity
are inherited from propositional equality — a parent vector *cannot fail* to
present an equivalence relation.

```agda
-- x ∼[ k ] y iff x and y lie in the same block of the k-th partition.
_∼[_]_ : Fin 6 → Fin 7 → Fin 6 → Type
x ∼[ k ] y = parent (θ k) x ≡ parent (θ k) y

-- Block membership is decidable by two root lookups.
∼-dec : ∀ k x y → Dec (x ∼[ k ] y)
∼-dec k x y = parent (θ k) x ≟ parent (θ k) y

-- The three equivalence laws, inherited from _≡_ on the roots.
∼-refl : ∀ k {x} → x ∼[ k ] x
∼-refl k = refl

∼-sym : ∀ k {x y} → x ∼[ k ] y → y ∼[ k ] x
∼-sym k = sym

∼-trans : ∀ k {x y z} → x ∼[ k ] y → y ∼[ k ] z → x ∼[ k ] z
∼-trans k = trans
```

#### Meets are intersections

The meet of two equivalence relations in `Eq(6)` is their intersection.  The
witness respects it on the nose: the relation of `k ∧ l` is exactly the
intersection of the relations of `k` and `l`, in both directions, decided over all
`7 · 7 · 6 · 6` instances.

```agda
-- The relation of a meet refines both arguments' relations.
meet-⊆ : ∀ k l x y → x ∼[ k ∧ l ] y → (x ∼[ k ] y) × (x ∼[ l ] y)
meet-⊆ = from-yes (all? λ k → all? λ l → all? λ x → all? λ y →
           ∼-dec (k ∧ l) x y →-dec (∼-dec k x y ×-dec ∼-dec l x y))

-- Conversely, a pair related by both arguments is related by the meet.
meet-⊇ : ∀ k l x y → (x ∼[ k ] y) × (x ∼[ l ] y) → x ∼[ k ∧ l ] y
meet-⊇ = from-yes (all? λ k → all? λ l → all? λ x → all? λ y →
           (∼-dec k x y ×-dec ∼-dec l x y) →-dec ∼-dec (k ∧ l) x y)
```

#### Joins are least upper bounds

The join of two equivalence relations in `Eq(6)` is the transitive closure of
their union — the least equivalence relation containing both.  Upper-boundedness
is a decided containment, exactly like the meets.

```agda
-- The relation of a join contains both arguments' relations.
join-⊇ : ∀ k l x y → (x ∼[ k ] y) ⊎ (x ∼[ l ] y) → x ∼[ k ∨ l ] y
join-⊇ = from-yes (all? λ k → all? λ l → all? λ x → all? λ y →
           (∼-dec k x y ⊎-dec ∼-dec l x y) →-dec ∼-dec (k ∨ l) x y)
```

Least-ness quantifies over *arbitrary* equivalence relations, so it cannot be a
finite decision by itself.  It reduces to one: an **alternating chain** from `x`
to `y` — hops each staying inside a `k`-block or an `l`-block — forces `x` and
`y` to be related in every equivalence relation containing both argument
relations, and chains of a fixed length are decidable.  The type
`Chain k l m x y`{.AgdaFunction} says `y` is reachable from `x` in at most `m`
hops.

```agda
-- One hop of an alternating chain: a k-block step or an l-block step.
Step : Fin 7 → Fin 7 → Fin 6 → Fin 6 → Type
Step k l x z = (x ∼[ k ] z) ⊎ (x ∼[ l ] z)

step-dec : ∀ k l x z → Dec (Step k l x z)
step-dec k l x z = ∼-dec k x z ⊎-dec ∼-dec l x z

-- Chains of at most m alternating hops from x to y.
Chain : Fin 7 → Fin 7 → ℕ → Fin 6 → Fin 6 → Type
Chain k l zero    x y = x ≡ y
Chain k l (suc m) x y = (x ≡ y) ⊎ (Σ[ z ∈ Fin 6 ] (Step k l x z × Chain k l m z y))

chain-dec : ∀ k l m x y → Dec (Chain k l m x y)
chain-dec k l zero    x y = x ≟ y
chain-dec k l (suc m) x y =
  (x ≟ y) ⊎-dec any? (λ z → step-dec k l x z ×-dec chain-dec k l m z y)
```

A chain is sound for any equivalence relation `T` containing the two argument
relations, by induction on its length.  `T` lives at an arbitrary universe level,
so the final theorem really does quantify over all of `Eq(6)` (and more).

```agda
module _ {ℓ : Level} (k l : Fin 7) {T : Fin 6 → Fin 6 → Type ℓ}
         (T-refl   :  ∀ {x} → T x x)
         (T-trans  :  ∀ {x y z} → T x y → T y z → T x z)
         (T-k      :  ∀ {x y} → x ∼[ k ] y → T x y)
         (T-l      :  ∀ {x y} → x ∼[ l ] y → T x y)
  where

  -- A single hop lands in T.
  step-sound : ∀ {x z} → Step k l x z → T x z
  step-sound (inj₁ x∼z) = T-k x∼z
  step-sound (inj₂ x∼z) = T-l x∼z

  -- A bounded chain lands in T, hop by hop.
  chain-sound : ∀ m {x y} → Chain k l m x y → T x y
  chain-sound zero    refl                 = T-refl
  chain-sound (suc m) (inj₁ refl)          = T-refl
  chain-sound (suc m) (inj₂ (z , s , c))   = T-trans (step-sound s) (chain-sound m c)
```

The one decided reachability fact: in every join partition, every point reaches
its block root by a chain of at most **four** hops through the two argument
partitions.  (Four is the exact worst case, attained at `k = 1F`, `l = 5F`,
`x = 5F`; the bound was computed alongside the witness and is re-verified here by
decision — a smaller bound would make this very decision compute to
`no`{.AgdaInductiveConstructor} and break compilation.)

```agda
-- Every point reaches its join-block root in at most four alternating hops.
join-root-chain : ∀ k l x → Chain k l 4 x (parent (θ (k ∨ l)) x)
join-root-chain = from-yes (all? λ k → all? λ l → all? λ x →
                    chain-dec k l 4 x (parent (θ (k ∨ l)) x))
```

Least-ness follows: two points related by the join partition share a root, each
reaches that root by a sound chain, and `T` closes the resulting path.

```agda
-- The join relation is contained in every equivalence relation containing
-- both arguments: it is the least upper bound in Eq(6).
join-⊆ : ∀ {ℓ} (k l : Fin 7) {T : Fin 6 → Fin 6 → Type ℓ} →
         (∀ {x} → T x x) →
         (∀ {x y} → T x y → T y x) →
         (∀ {x y z} → T x y → T y z → T x z) →
         (∀ {x y} → x ∼[ k ] y → T x y) →
         (∀ {x y} → x ∼[ l ] y → T x y) →
         ∀ {x y} → x ∼[ k ∨ l ] y → T x y
join-⊆ {ℓ} k l {T} T-refl T-sym T-trans T-k T-l {x} {y} x∼y =
  T-trans (subst (T x) x∼y x-chain) (T-sym y-chain)
  where
  x-chain : T x (parent (θ (k ∨ l)) x)
  x-chain = chain-sound k l T-refl T-trans T-k T-l 4 (join-root-chain k l x)
  y-chain : T y (parent (θ (k ∨ l)) y)
  y-chain = chain-sound k l T-refl T-trans T-k T-l 4 (join-root-chain k l y)
```

Together, `θ-injective`{.AgdaFunction}, `meet-⊆`{.AgdaFunction}/`meet-⊇`{.AgdaFunction},
`join-⊇`{.AgdaFunction}, and `join-⊆`{.AgdaFunction} say precisely that
`θ`{.AgdaFunction} is a lattice embedding of `L7` into `Eq(6)`: the image of a meet
is the meet (intersection) of the images, and the image of a join is the join
(least upper bound) of the images.  This is the library's machine-checked
Pudlák–Tůma witness for its distinguished open lattice, on a base set of minimal
size.
