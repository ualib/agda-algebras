---
layout: default
file: "src/FLRP/Assumptions.lagda.md"
title: "FLRP.Assumptions module (The Agda Universal Algebra Library)"
date: "2026-07-20"
author: "the agda-algebras development team"
---

### The registry of classical assumptions of the FLRP program

This is the [FLRP.Assumptions][] module of the [Agda Universal Algebra Library][].

The [Agda Universal Algebra Library][] is postulate-free, confined to
[*Safe Agda*](https://agda.readthedocs.io/en/v2.8.0-r3/language/safe-agda.html#safe-agda),
and the FLRP tree is no execption.  Where a result genuinely depends on a classical
theorem, that theorem is never introduced as a `postulate`; it is stated as an
*explicit hypothesis* and threaded through the results that consume it.

The present module is the single place these hypotheses are *named, documented, and
given their logical strength*, so that the classical content of the FLRP research
program is auditable at one site rather than smeared across the development.[^1]

**Entry 1**: the congruence-completeness bridge.  This is the *single* classical
assumption of the two-layer discipline: the one place a result may cross from the
semantic congruence layer (Layer S, `Con`{.AgdaFunction}) to the decidable layer
(Layer D, `DecCon`{.AgdaFunction}).  It is registered here as
`CongruenceCompleteness`{.AgdaFunction} `𝑨`.

+  **Meaning**.  Every *semantic* congruence of `𝑨`{.AgdaBound} is `≑`{.AgdaFunction}
   to a *decidable* one.  (`≑`{.AgdaFunction} is mutual containment.)

+  **Source**.  It is exactly the `complete`{.AgdaField} field of
   `FiniteCongruences`{.AgdaRecord} of [Setoid.Congruences.Finite.Basic][], with the
   finite list and its membership proof forgotten (the list side is *constructive* —
   see below), so `fromFiniteCongruences`{.AgdaFunction} extracts it from the canonical
   record.

+  **Strength**.  It sits strictly *between weak excluded middle and excluded middle*
   at the working relation level.  The lower bound is the no-go theorem
   `chain₂-ConIso→WLEM`{.AgdaFunction} / `chain₂-Representable→WLEM`{.AgdaFunction} of
   [FLRP.Problem][]: on a nontrivial algebra the bridge lets an oracle congruence be
   decided, yielding weak excluded middle.  The upper bound is that full excluded
   middle at the working level supplies it.[^2]

The constructive *complement* of this assumption is already discharged with no axiom:
the finite list of decidable congruences and its completeness *for the decidable layer*
is `FiniteCongruencesᵈ`{.AgdaRecord} of [Setoid.Congruences.Finite.Decidable][], built
from carrier- and signature-finiteness alone.  `toFiniteCongruences`{.AgdaFunction}
below makes this precise: adjoining `CongruenceCompleteness`{.AgdaFunction} to that
free constructive data reconstitutes the full semantic
`FiniteCongruences`{.AgdaRecord}, so the assumption is exactly the classical delta
between the two layers, no more, no less.

**Entry 2** (*retired*): Kurzweil–Netter duality.  The class of representable
lattices is closed under dualization — proved by Kurzweil (1985) for intervals
in solvable groups and by Netter (1986) in general, the latter possibly never
published.  Registered here as `KurzweilNetterDuality`{.AgdaFunction} while a
formal reproof was pending, the entry is **retired as an assumption**: issue
#502's [FLRP.KurzweilNetter.Duality][] proves the statement outright from the
properties of the base group the argument actually uses, the only remaining
classical ingredient being Entry 4.  The statement types remain here as the
theorem's canonical name.[^3]

**Entry 3**: the Pálfy–Pudlák theorem.  Every finite lattice is a congruence
lattice of a finite algebra *if and only if* every finite lattice is an interval in
the subgroup lattice of a finite group.  The FLRP program consumes one direction of
it, and only at the level of the two *statements*, which is exactly how the theorem
is used: exhibiting a finite lattice that is no interval refutes the group-side
statement, hence the algebra-side one.  It is registered as
`PalfyPudlak`{.AgdaFunction}.[^4]

**Entry 4**: Kurzweil interval surjectivity.  For a finite *nonabelian simple*
group `S`, every subgroup between the diagonal `D` and the full power `Sⁿ` is a
partition subgroup `K_π` — the surjectivity half of Kurzweil's lemma
`[D , Sⁿ] ≅ Eq(n)′`, whose dual-embedding half is proved outright in
[Classical.Structures.Group.PartitionSubgroup][].  It is registered as
`KurzweilSurjectivityAt`{.AgdaFunction}, in the witness-producing form defined
by [FLRP.KurzweilInterval][].

The module is structured as *per-assumption statement definitions* (rather than one
monolithic record) precisely so that entries can be appended without disturbing one
another, and downstream results take whichever entry they need as an ordinary
argument.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Assumptions where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Membership.Propositional    using  ( _∈_ )
open import Data.Nat.Base                         using  ( ℕ )
open import Data.Product                          using  ( _×_ ; _,_ ; Σ-syntax
                                                         ; proj₁ ; proj₂ )
open import Function                              using  (_∘_)
open import Level                                 using  ( Level ; _⊔_ ; 0ℓ )
                                                  renaming ( suc to lsuc )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Small.Structures.Lattice    using  ( Lattice )
open import Classical.Structures.Group.Basic      using  ( Group )
open import Classical.Structures.Lattice.Dual     using  ( dualLattice )
open import FLRP.Enforceable                      using  ( GroupFLRP-Statement )
open import FLRP.KurzweilInterval                 using  ( module KurzweilInterval )
open import FLRP.Problem                          using  ( FLRP-Statement )
open import FLRP.Representable                    using  ( Representableᵈ )
open import Overture                              using  ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic                 using  ( Algebra )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra )
open import Setoid.Signatures.Finite              using  ( FiniteSignature )
open import Setoid.Congruences.Basic              using  ( Con )
open import Setoid.Congruences.Lattice            using  ( _≑_ )
open import Setoid.Congruences.Finite.Basic       using  ( DecCon ; FiniteCongruences )
open import Setoid.Congruences.Finite.Decidable   using  ( FiniteCongruencesᵈ
                                                         ; FiniteAlgebra→FiniteCongruencesᵈ )

private variable α ρ : Level
```
-->

#### Entry 1: the congruence-completeness bridge

Throughout we fix an algebra `𝑨`{.AgdaBound} and work at its
**working congruence level** `ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` — the absorbing level at which the
decidable-layer machinery of [Setoid.Congruences.Finite.Basic][] and
[Setoid.Congruences.Finite.Decidable][] lives, and the level at which the `complete`
field of `FiniteCongruences`{.AgdaRecord} quantifies.

```agda
module _ {𝑆 : Signature 𝓞 𝓥}(𝑨 : Algebra {𝑆 = 𝑆} α ρ) where
  private
    ℓ : Level
    ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ
```

`CongruenceCompleteness`{.AgdaFunction} `𝑨` is the assumption itself; it is a
function that, given *any* semantic congruence `φ`{.AgdaBound}, produces a decidable
congruence `≑`{.AgdaFunction} to it.

This is the `complete`{.AgdaField} field of `FiniteCongruences`{.AgdaRecord} with the
list `cons`{.AgdaField} and the membership proof `d ∈ cons`{.AgdaFunction} dropped;
those record the *finiteness* of the collection of decidable congruences, which is
constructive (`FiniteCongruencesᵈ`{.AgdaRecord}), whereas the classical content is
precisely the existence of a decidable `≑`-representative for a congruence that need
carry no decision procedure of its own.

```agda
  -- For each semantic congruence φ, there exists a decidable congruence d such that φ ≑ d.
  CongruenceCompleteness : Type (lsuc ℓ)
  CongruenceCompleteness = (φ : Con 𝑨 ℓ) → Σ[ (d , _) ∈ DecCon 𝑨 ℓ ] φ ≑ d
```

**The source**.  A `FiniteCongruences`{.AgdaRecord} witness — the canonical form of
the assumption in the library — yields the bridge by forgetting the list and its
membership proof.  This is the direction a consumer already in posession of the full
record would use.

```agda
  fromFiniteCongruences : FiniteCongruences 𝑨 → CongruenceCompleteness
  fromFiniteCongruences 𝑪 φ = witness φ , witness≑ φ
    where open FiniteCongruences 𝑪 using ( witness ; witness≑ )
  -- Recall, `witness φ` is d and `witness≑ φ` is the proof of `φ ≑ proj₁ d`

```

**The classical delta**.  Conversely, adjoining the bridge to the *free constructive*
data of a finite finitary algebra — its carrier finiteness
(`FiniteAlgebra`{.AgdaRecord}) and signature finiteness (`FiniteSignature`{.AgdaRecord}),
from which `FiniteAlgebra→FiniteCongruencesᵈ`{.AgdaFunction} builds a complete list of
*decidable* congruences with no axiom — reconstitutes the full semantic
`FiniteCongruences`{.AgdaRecord}.

So `CongruenceCompleteness`{.AgdaFunction} is neither more nor less than the
classical content of "finite" for congruence-lattice purposes: it is the gap
between Layer D and Layer S, and nothing else.

The list is the constructive `consᵈ`{.AgdaField}; completeness chains the bridge's
`≑`{.AgdaFunction} into the decidable-layer completeness `completeᵈ`{.AgdaField} by
transitivity.

```agda
  toFiniteCongruences : CongruenceCompleteness
    → FiniteAlgebra 𝑨 → FiniteSignature 𝑆 → FiniteCongruences 𝑨
  toFiniteCongruences cc 𝑭 𝑺 = record { cons = consᵈ ; complete = comp }
    where
    open FiniteCongruencesᵈ (FiniteAlgebra→FiniteCongruencesᵈ 𝑭 𝑺)
      using ( consᵈ ; witnessᵈ ; witnessᵈ∈ ; witnessᵈ≑ )

    comp : (φ : Con 𝑨 ℓ) → Σ[ e ∈ DecCon 𝑨 ℓ ] e ∈ consᵈ × φ ≑ proj₁ e
    comp φ = e , witnessᵈ∈ d , φ≑e
      where
      d : DecCon 𝑨 ℓ
      d = cc φ .proj₁

      φ≑d : φ ≑ d .proj₁
      φ≑d = cc φ .proj₂

      e : DecCon 𝑨 ℓ
      e = witnessᵈ d

      d≑e : d .proj₁ ≑ e .proj₁
      d≑e = witnessᵈ≑ d

      φ≑e : φ ≑ e .proj₁
      φ≑e = d≑e .proj₁ ∘ φ≑d .proj₁ , φ≑d .proj₂ ∘ d≑e .proj₂
```

#### Entry 2: Kurzweil–Netter duality (retired)

The **theorem of Kurzweil and Netter**: if a finite lattice is representable as
the congruence lattice of a finite algebra, then so is its dual.  Kurzweil proved
the group-interval case (H. Kurzweil, *Endliche Gruppen mit vielen Untergruppen*,
J. reine angew. Math. 356 (1985) 140–160); his student Netter proved the general
statement (R. Netter, 1986), in an article that may never have been published.
The formalized argument is the one presented in
`docs/papers/fin-lat-rep/SmallLatticeReps.tex` § "Lattice duals: the theorem of
Kurzweil and Netter", following Pálfy's 2009 lectures: represent the dual of
`Eq(n)` as the interval `[D , Sⁿ]` in the subgroup lattice of a power of a
nonabelian simple group `S`, transport along the congruence lattice of the
transitive `Sⁿ`-set on `Sⁿ/D`, and cut down to the desired dual by expanding the
algebra with lifted operations.

+  **Meaning**.  `KurzweilNetterDualityAt`{.AgdaFunction} `𝑳` says: from a
   decidable representation of `𝑳`{.AgdaBound}, one can produce a decidable
   representation of `dualLattice 𝑳`{.AgdaFunction}
   ([Classical.Structures.Lattice.Dual][]).  The ∀-form
   `KurzweilNetterDuality`{.AgdaFunction} is the full theorem.

+  **Status: retired as an assumption** (issue #502).
   `kurzweilNetterDuality`{.AgdaFunction} of [FLRP.KurzweilNetter.Duality][]
   *proves* `KurzweilNetterDuality`{.AgdaFunction} outright, parameterized by
   the properties of the base group the argument actually uses — a finite
   carrier with decidable equality, a nontriviality witness, and Entry 4's
   surjectivity family — and `dual-Representableᵈ`{.AgdaFunction} of
   [FLRP.Closure][] is rewired to that theorem.  Nothing consumes this entry
   as a hypothesis any more; the definitions below remain as the canonical
   *statement* of the theorem (they are its conclusion's type).  The residual
   classical content is exactly Entry 4 (retirement tracked by issue #522)
   plus the instantiation of `𝒮` at a concrete finite nonabelian simple group
   (tracked separately; `A₅` needs the simplicity predicates of issue #512).

+  **Layer**.  The statement is at Layer D (`Representableᵈ`{.AgdaRecord}),
   the program's working notion per [ADR-008][]; the classical statement is the
   Layer-S reading, and the two coincide classically through Entry 1.  As
   anticipated at registration, the formal proof produces the Layer-D form
   directly: the construction is finite and explicit.

+  **Size**.  The construction represents the dual on an algebra of
   `|S|ⁿ⁻¹ ≥ 60ⁿ⁻¹` elements (for an `n`-element original), which is why the
   census keeps dual entries conditional rather than materializing concrete
   certificate algebras: the theorem makes their *statements* assumption-free
   (modulo Entry 4) without bringing the certificates in reach.

```agda
-- Entry 2, per-lattice form: a decidable representation of 𝑳 yields one of its
-- dual.  Proved by FLRP.KurzweilNetter.Duality; retained as the statement type.
KurzweilNetterDualityAt : Lattice → Type (lsuc 0ℓ)
KurzweilNetterDualityAt 𝑳 = Representableᵈ 𝑳 → Representableᵈ (dualLattice 𝑳)

-- The theorem of Kurzweil (1985) and Netter (1986), as a statement.
KurzweilNetterDuality : Type (lsuc 0ℓ)
KurzweilNetterDuality = (𝑳 : Lattice) → KurzweilNetterDualityAt 𝑳
```

#### Entry 3: the Pálfy–Pudlák theorem

The **theorem of Pálfy and Pudlák** (P. P. Pálfy and P. Pudlák, *Congruence
lattices of finite algebras and intervals in subgroup lattices of finite groups*,
Algebra Universalis 11 (1980) 22–27) states the equivalence of

+  **(A)** every finite lattice is isomorphic to the congruence lattice of a finite
   algebra — the type `FLRP-Statement`{.AgdaFunction} of [FLRP.Problem][]; and
+  **(B)** every finite lattice is isomorphic to an interval in the subgroup lattice
   of a finite group — the type `GroupFLRP-Statement`{.AgdaFunction} of
   [FLRP.Enforceable][].

+  **Meaning**.  `PalfyPudlak`{.AgdaFunction} is the direction (A) `→` (B), which is
   the one the program consumes: its contrapositive turns a lattice proved to be no
   interval into a negative answer for the FLRP.  The converse direction (B) `→` (A)
   is not needed anywhere and is deliberately not registered.

+  **Granularity**.  The entry is *statement-level*, matching the theorem as
   published: it says nothing about which particular lattice fails, only that the
   two universally quantified statements stand or fall together.  A per-lattice
   reading ("this congruence lattice is an interval") would be a stronger assumption
   and is not assumed here — which is why the strategy meta-theorem of
   [FLRP.Parachute.Theorems][] concludes `¬ FLRP-Statement`{.AgdaFunction} rather
   than non-representability of the parachute itself.

+  **Status and retirement path**.  A classically proven theorem imported pending
   formalization.  Its proof needs the minimal-cardinality argument (a minimal
   algebra representing a lattice has only permutations among its unary polynomials,
   so its congruence lattice is that of a transitive G-set) together with the
   Pálfy–Pudlák correspondence `Con (G ↷ G/H) ≅ [H , G]`; the latter is work package
   WP-3 and the former is the remaining gap.

+  **Layer**.  Layer S on both sides, as published.  The Layer-D reading follows by
   Entry 1 where a consumer needs it.

```agda
-- Entry 3: statement (A) of Pálfy–Pudlák implies statement (B).
PalfyPudlak : Type (lsuc 0ℓ)
PalfyPudlak = FLRP-Statement → GroupFLRP-Statement
```

#### Entry 4: Kurzweil interval surjectivity

**Kurzweil's surjectivity lemma**: if `S` is a finite nonabelian simple group,
then every subgroup of `Sⁿ` containing the diagonal `D` is a partition subgroup
`K_π = { y ∣ ker π ≤ ker y }`.  This is the *onto* half of the isomorphism
`[D , Sⁿ] ≅ Eq(n)′` (H. Kurzweil, *Endliche Gruppen mit vielen Untergruppen*,
J. reine angew. Math. 356 (1985) 140–160 — the same article behind Entry 2's
group-interval case); the write-ups this library follows
(`docs/papers/fin-lat-rep/SmallLatticeReps.tex` § "Lattice duals", Lemma
`lem:latt-duals`, and DeMeo's thesis § 2.2) prove the dual order embedding and
cite the surjectivity without reproof.  The embedding half is *proved* in
[Classical.Structures.Group.PartitionSubgroup][]; this entry is exactly the
remaining classical delta.

+  **Meaning**.  `KurzweilSurjectivityAt`{.AgdaFunction} `𝒮` `n` says: every
   element of the respecting upper interval `[D , Sⁿ]` (an
   `Interval≈`{.AgdaFunction} of the `UpperInterval`{.AgdaModule} at the
   diagonal) is extensionally `K_π` for a *produced* partition `π` — the Σ-form
   defined in [FLRP.KurzweilInterval][], which is precisely what the inverse map
   of `kurzweilIntervalIso`{.AgdaFunction} consumes.

+  **Side condition**.  The statement type is defined for an arbitrary
   `𝒮 : Group 0ℓ 0ℓ` — and for arbitrary `𝒮` it is *false* (for `S = ℤ₃` and
   `n = 3` the tuples with `x₀ x₂ = x₁²` form a non-partition subgroup above the
   diagonal).  The classical theorem asserts the instances where `𝒮` is finite
   nonabelian simple, and consumers must instantiate it there; the side
   condition stays in prose because the library does not yet define simplicity
   predicates (issue #512 owns them), and making it formal is part of this
   entry's retirement.

+  **Status and retirement path**.  A classically proven theorem imported
   pending formalization.  The missing mathematics is the normal-subgroup
   structure theory of powers of a nonabelian simple group (normal subgroups of
   `Sⁿ` are partial products; subdirect subgroups containing the diagonal
   collapse blockwise), a follow-up flagged in issue #521.  On completion this
   entry retires, `kurzweilIntervalIso`{.AgdaFunction} holds outright at simple
   instantiations, and the Kurzweil–Netter route of issue #502 loses one of its
   two imported steps toward retiring Entry 2.

+  **Layer**.  Layer S, on the respecting interval `Interval≈`{.AgdaFunction}.
   Over a decidable interval element (`Intervalᵈ`{.AgdaFunction}) with a finite
   base group the partition is computable as the kernel meet of the member
   tuples, so a formal proof is expected to produce the Layer-D reading
   directly, mirroring Entry 2's layer note.

```agda
-- Entry 4, per-instance form: every subgroup in [D , Sⁿ] is a partition
-- subgroup, with the partition produced as data.  Classically true for 𝒮 a
-- finite nonabelian simple group; consumers instantiate it there.
KurzweilSurjectivityAt : Group 0ℓ 0ℓ → ℕ → Type (lsuc 0ℓ)
KurzweilSurjectivityAt 𝒮 n = KurzweilInterval.KurzweilSurjectivity 𝒮 n
```

--------------------------------------

[^1]: This is the assumption-registry discipline of [ADR-008][] and the FLRP roadmap.

[^2]: Pinning the exact strength is a side question the program does not need
      (see `docs/notes/flrp-two-layer-congruences.md` § 2.1, L4).

[^3]: **WP-5: closure toolkit** formalized product and ordinal-sum closure of
      decidable representability outright in [FLRP.Closure][] and registered
      duality here as Entry 2 (see
      [`docs/notes/flrp-research-roadmap.md`](docs/notes/flrp-research-roadmap.md) § 7
      and GitHub [Issue #456](https://github.com/ualib/agda-algebras/issues/456)).
      The work package's stretch goal — the formal reproof — landed with GitHub
      [Issue #502](https://github.com/ualib/agda-algebras/issues/502), retiring
      the entry.

[^4]: Registered by **RP-1** (GitHub
      [Issue #458](https://github.com/ualib/agda-algebras/issues/458)), which needs it
      for the strategy meta-theorem of [FLRP.Parachute.Theorems][]; see
      [`docs/notes/flrp-rp1-parachutes.md`](docs/notes/flrp-rp1-parachutes.md).
