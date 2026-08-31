---
layout: default
file: "src/FLRP/WreathNoGo.lagda.md"
title: "FLRP.WreathNoGo module (The Agda Universal Algebra Library)"
date: "2026-07-27"
author: "the agda-algebras development team"
---

### The wreath no-go: Lemma 3.3 and the dead-end question

This is the [FLRP.WreathNoGo][] module of the [Agda Universal Algebra Library][].

This module is the formal face of research phase RP-4: the note's **Lemma 3.3**[^1],
its corollary that classes omitting wreath products are not core-free interval
enforceable by group-representable lattices, and the statements that frame the
phase's open **dead-end question**, "Can a property and its negation both be cf-IE
by group-representable lattices?"

**The theorem and its proof shape**.

*Lemma 3.3*.  If `P` is a cf-IE property, enforced by a group representable
lattice, then for every finite nonabelian simple group `S`, some wreath product
`S ≀ Ū` has property `P`.

The proof applies Kurzweil's construction twice.  From a core-free representation
`[H , G] ≅ 𝑳`, the wreath product `U = S ≀ G` over the coset action of `G` on
`G / H` carries the *dual* lattice as an upper interval, `[D Ḡ , U] ≅ 𝑳′`, over
the subgroup `D Ḡ` of diagonal-based elements; crucially, `D Ḡ` is again
*core-free*, so the construction can be repeated: `[D₁ Ū , S ≀ Ū] ≅ 𝑳″ = 𝑳` is
again a core-free representation, of the original lattice, and cf-IE forces
`P (S ≀ Ū)`.

**What is imported, and what is proved**.  The honest split, per the `--safe`
discipline of the roadmap (§ 6) and the per-entry registry style of
[FLRP.Assumptions][] is as follows:

+  **Imported: Entry 5** (`KurzweilWreathInterval`{.AgdaFunction}, defined here,
   registered as `KurzweilWreathIntervalAt`{.AgdaFunction}).

   From a core-free representation, over a *finite* group, of a lattice `𝑳` with
   two distinct elements, Kurzweil's construction yields the enumerated coset
   action of `𝒢` on the cosets of `H` (a `RightAction`{.AgdaRecord} on `Fin (2 + m)`
   with the pointed `IsCosetAction`{.AgdaRecord} specification) and the interval
   isomorphism `[D Ḡ , S ≀ G] ≅ 𝑳′`.

   The isomorphism is Kurzweil's theorem (the same 1985 article behind Entries 2
   and 4); the enumeration of the coset space, and the carrier finiteness of the
   wreath the construction builds, are elementary finiteness bookkeeping the
   library cannot yet perform.  All parts are documented in the registry entry,
   with the retirement path split accordingly.

+  **Proved: the technical heart**.

   Core-freeness preservation (`Diag≀-coreFree`{.AgdaFunction} of
   [Classical.Structures.Group.Wreath][]) and the kernel–core correspondence
   (`coreFree→faithful`{.AgdaFunction} of
   [Classical.Structures.Group.IndexAction][]); so faithfulness of the provided
   action is *derived* from core-freeness of the representation, not assumed.

   The preservation proof also repairs the note's index-hypothesis gap; see the
   Wreath module header and `docs/notes/flrp-rp4-wreath.md` § 4.

+  **Proved: the assembly**.

   The double application (Lemma 3.3, `cfIE-must-have-wreaths`{.AgdaFunction}),
   the omission corollary (`omits-wreaths→not-cfIE`{.AgdaFunction}), the
   wreath-richness constraint on contradictory pairs
   (`contradictory-pair-wreaths`{.AgdaFunction}), and the reduction of the
   dead-end question to statement (C) of the parachute program
   (`statement-C→no-contradictory-pair`{.AgdaFunction}).

**Where the two-element hypothesis comes from**.

If `𝑳` is trivial then `[H , G] ≅ 𝑳` forces `H = G`, the coset space has one
point, and `D Ḡ` is *all* of `S ≀ G`; the wreath interval degenerates and the
lemma is false (cf-IE by the one-point lattice constrains only the trivial group).
Two distinct elements of `𝑳` rule this out: classically `n = |G : H| ≥ 2`, which
is why Entry 5 produces an action on `Fin (2 + m)`.  The hypothesis transports to
the dual (`nontrivial-dual`{.AgdaFunction}), which is what keeps the second
application fed.

**The nonabelian-simple side condition**.

The formal hypotheses on `𝒮` are the two fragments the core-freeness argument
consumes (a non-identity element and a trivial center,
`NontrivialCenterless`{.AgdaRecord}).  The library's simplicity notion
([Classical.Structures.Group.Simple][]) discharges the record at any nonabelian
simple group with decidable equality
(`nonabelianSimple→nontrivialCenterless`{.AgdaFunction} below), so consumers can
instantiate `𝒮` through the notion instead of threading the fragments by hand.

Kurzweil's interval theorem needs full finite nonabelian simplicity, which stays a
prose side condition of Entry 5, exactly as in Entry 4.  Finiteness of the
*represented* group, by contrast, is a formal antecedent of the entry
(a `FiniteAlgebra`{.AgdaRecord} witness); only the finiteness of `𝒮` stays in
prose alongside simplicity.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.WreathNoGo where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using  ( ⊥ )
open import Data.Fin.Base                          using  ( Fin ; suc )
open import Data.Fin.Patterns                      using  ( 0F ; 1F )
open import Data.Fin.Properties                    using  ( _≟_ )
open import Data.Nat.Base                          using  ( ℕ ; _+_ )
open import Data.Product                           using  ( Σ-syntax ; _×_ ; _,_
                                                          ; proj₁ ; proj₂ ; ∃-syntax )
open import Level                                  using  ( Level ; 0ℓ ; _⊔_ )
                                                   renaming ( suc to lsuc )
open import Relation.Binary                        using  ( Setoid )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ )
open import Relation.Nullary                       using  ( ¬_ )
open import Relation.Unary                         using  ( Pred )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Small.Structures    using  ( Lattice )
open import Classical.Structures.Group    using  ( Group ; module Group-Op
                                                 ; RightAction ; IsCosetAction
                                                 ; module ActionKernel ; _≀ᵍ_
                                                 ; IsSubgroup ; module WreathProduct
                                                 ; module Simple )
open import Classical.Structures.Lattice  using  ( dualLattice )
open import FLRP.Enforceable              using  ( cfIE ; CoreFree
                                                 ; CoreFreeRepresentable
                                                 ; GroupRepresentable ; GroupProperty
                                                 ; IntervalIso ; Statement-C
                                                 ; TwoBigCanopies ; Nontrivial
                                                 ; HasThreeDistinct
                                                 ; threeDistinct→nontrivial )
open import FLRP.Problem                  using  ( FiniteLattice ; toLattice )
open import Setoid.Algebras               using  ( 𝕌[_] ; 𝔻[_] ; FiniteAlgebra )

open GroupRepresentable
```
-->

#### Two distinct elements, and their transport to the dual

**The nontriviality side condition on the enforcing lattice** is
`Nontrivial`{.AgdaFunction} of [FLRP.Enforceable][], where it now lives
beside its three-element sibling as a guard of statement (C).  The dual lattice
of [Classical.Structures.Lattice.Dual][] lives on the *same* carrier setoid, so
the witness transports unchanged.

```agda
-- The dual shares carrier and equality, so the witness transports as-is.
nontrivial-dual : (𝑳 : Lattice) → Nontrivial 𝑳 → Nontrivial (dualLattice 𝑳)
nontrivial-dual 𝑳 w = w
```

#### The nonabelian-simple fragments

The two properties of the base group the core-freeness argument consumes are a
non-identity element and triviality of the center.  A finite nonabelian simple
group has both (it is nontrivial, and its center is a proper normal subgroup,
hence trivial); a nontrivial centerless group is automatically nonabelian, which
is what the repaired index argument uses.

```agda
record NontrivialCenterless (𝒮 : Group 0ℓ 0ℓ) : Type 0ℓ where
  open Group-Op 𝒮 using ( _∙_ ; ε )
  open Setoid 𝔻[ 𝒮 .proj₁ ] using ( _≈_ )

  field
    elt         : 𝕌[ 𝒮 .proj₁ ]
    elt≉ε       : ¬ elt ≈ ε
    centerless  : ∀ d → (∀ t → t ∙ d ≈ d ∙ t) → d ≈ ε
```

The record is exactly what the library's nonabelian-simple interface of
[Classical.Structures.Group.Simple][] proves: the interface's non-commuting pair
supplies the non-identity element, and its center-triviality theorem supplies
`centerless`{.AgdaField}, positively, given stability of identity equations
(which decidable equality supplies, so every concrete finite instance qualifies).
Consumers holding a certified nonabelian simple group therefore discharge the
record here once, instead of exhibiting the two fragments per instance.

```agda
-- Nonabelian simple, with stable identity equations, implies nontrivial
-- and centerless.  The stability antecedent is the constructive caveat
-- recorded in the Simple module's design note.
nonabelianSimple→nontrivialCenterless : (𝒮 : Group 0ℓ 0ℓ)
  → Simple.Stable-≈ε 𝒮 0ℓ
  → Simple.IsNonabelianSimple 𝒮 0ℓ
  → NontrivialCenterless 𝒮
nonabelianSimple→nontrivialCenterless 𝒮 st nas = record
  { elt         = S.elt nas
  ; elt≉ε       = S.elt≉ε nas
  ; centerless  = λ d central → S.center-trivial st nas d (λ x _ → ≈sym (central x))
  }
  where
  module S = Simple 𝒮 0ℓ
  open Setoid 𝔻[ 𝒮 .proj₁ ] using () renaming ( sym to ≈sym )
```

#### Entry 5: Kurzweil's wreath interval

**The data Kurzweil's construction attaches to a core-free representation of a
finite group**: the enumerated coset action (on an index set of at least two
points; the record carries `2 + degree`), its pointed coset-action specification
tying it to `H`, the interval isomorphism `[D Ḡ , S ≀ G] ≅ 𝑳′` onto the dual of
the represented lattice, and carrier finiteness of the wreath product the
construction builds — the field that feeds the entry's own finiteness antecedent
at the second application.

```agda
record WreathIntervalData
  (𝒮     : Group 0ℓ 0ℓ)
  (𝑳     : Lattice)
  (𝒢     : Group 0ℓ 0ℓ)
  (H     : Pred 𝕌[ 𝒢 .proj₁ ] 0ℓ)
  (H-sg  : IsSubgroup 𝒢 H) : Type (lsuc 0ℓ) where
  field
    degree    : ℕ
    action    : RightAction (Fin (2 + degree)) 𝒢
    cosets    : IsCosetAction action H
    interval  : IntervalIso  (𝒮 ≀ᵍ action)
                             (WreathProduct.Diag≀ 𝒮 action)
                             (WreathProduct.Diag≀-isSubgroup 𝒮 action)
                             (dualLattice 𝑳)
    finite    : FiniteAlgebra (proj₁ (𝒮 ≀ᵍ action))
```

**The statement type of Entry 5 of the assumptions registry** ([FLRP.Assumptions][]):
every core-free representation of a lattice with two distinct elements *over a
finite group* extends to the full wreath-interval package.  The finiteness
antecedent (a `FiniteAlgebra`{.AgdaRecord} witness for the represented group) is
what keeps the statement exactly the cited finite theorem: without it the type
would also quantify over infinite-index core-free representations, where no
finite coset enumeration exists and the statement is false.  The registry entry
documents source, side conditions, and the split retirement path; the classical
theorem asserts the instances where `𝒮` is a finite nonabelian simple group, and
consumers must instantiate it there.

```agda
KurzweilWreathInterval : Group 0ℓ 0ℓ → Type (lsuc 0ℓ)
KurzweilWreathInterval 𝒮 =
  (𝑳          : Lattice)
  (𝒢@(𝑮 , _)  : Group 0ℓ 0ℓ)
  (H          : Pred 𝕌[ 𝑮 ] 0ℓ)
  (H-sg       : IsSubgroup 𝒢 H)
  → FiniteAlgebra 𝑮
  → CoreFree 𝒢 H H-sg
  → IntervalIso 𝒢 H H-sg 𝑳
  → Nontrivial 𝑳
  → WreathIntervalData 𝒮 𝑳 𝒢 H H-sg
```

#### Core-freeness of the wreath representation

**The formal content that makes the double application go**: the wreath package
of a *core-free* representation is again core-free.  Faithfulness of the
provided action is derived from core-freeness through the kernel–core
correspondence, and the preservation theorem of
[Classical.Structures.Group.Wreath][] does the rest; the two-point index
hypothesis is discharged by `fin-another`{.AgdaFunction} on `Fin (2 + m)`,
and decidable index equality by `Data.Fin`'s `_≟_`.

```agda
-- Every index of Fin (2 + m) has a distinct companion.
fin-another : ∀ {m} (i : Fin (2 + m)) → Σ[ j ∈ Fin (2 + m) ] ¬ j ≡ i
fin-another 0F       = 1F , λ ()
fin-another (suc i)  = 0F , λ ()

module _ {𝒮 𝑳 𝒢} {H : Pred 𝕌[ proj₁ 𝒢 ] 0ℓ} {H-sg : IsSubgroup 𝒢 H}
  (k : WreathIntervalData 𝒮 𝑳 𝒢 H H-sg) where
  open WreathIntervalData k

  -- The wreath representation over a core-free representation is core-free.
  wreath-coreFree : NontrivialCenterless 𝒮 → CoreFree 𝒢 H H-sg
    → CoreFree  (𝒮 ≀ᵍ action)
                (WreathProduct.Diag≀ 𝒮 action)
                (WreathProduct.Diag≀-isSubgroup 𝒮 action)
  wreath-coreFree nc cf = CF.Diag≀-coreFree
    where
    open NontrivialCenterless nc

    -- Core-freeness of H makes the coset action faithful.
    faithful : RightAction.Faithful action
    faithful = ActionKernel.coreFree→faithful 𝒢 H H-sg action cosets cf

    module W   = WreathProduct 𝒮 action
    module CF  = W.CoreFreeness _≟_ fin-another elt elt≉ε centerless faithful
```

#### Lemma 3.3: cf-IE properties must have wreath products

**The note's Lemma 3.3, by the double application**.

The first application turns the given core-free representation of `𝑳` into a
core-free representation of `𝑳′` on `[D Ḡ , 𝒮 ≀ 𝒢]`; the second turns that
into a core-free representation of `𝑳″` on `[D₁ Ū , 𝒮 ≀ Ū]` with
`Ū = 𝒮 ≀ 𝒢`.

Dualization swaps the two lattice operations, so dualizing twice restores them
definitionally, and the second interval isomorphism *is* an interval isomorphism
with `𝑳` (no transport is needed) to which cf-IE applies.

Carrier finiteness rides on the entry's own output: the given representation's
`FiniteAlgebra`{.AgdaRecord} witness feeds the first application, and the wreath
finiteness the entry returns feeds the second.

```agda
cfIE-must-have-wreaths :
  ∀ {ℓP} (P : GroupProperty ℓP) (𝑳 : Lattice) (𝒮 : Group 0ℓ 0ℓ)
  → NontrivialCenterless 𝒮
  → KurzweilWreathInterval 𝒮
  → cfIE P 𝑳
  → (r : CoreFreeRepresentable 𝑳)
  → FiniteAlgebra (proj₁ (CoreFreeRepresentable.rep r .grp))
  → Nontrivial 𝑳
  → ∃[ 𝒰 ] ∃[ m ] Σ[ A ∈ RightAction (Fin (2 + m)) 𝒰 ] P (𝒮 ≀ᵍ A)
cfIE-must-have-wreaths P 𝑳 𝒮 nc kwi cf-ie r fin two =
  𝒰 , K₂.degree , K₂.action , P-holds
  where
  open CoreFreeRepresentable r
  -- First application: a core-free representation of 𝑳′ on the first wreath.
  k₁ : WreathIntervalData 𝒮 𝑳 (rep .grp) (rep .sub) (rep .isSubgroup)
  k₁ = kwi 𝑳 (rep .grp) (rep .sub) (rep .isSubgroup) fin cf (rep .interval-iso) two

  module K₁ = WreathIntervalData k₁

  𝒰 : Group 0ℓ 0ℓ
  𝒰 = 𝒮 ≀ᵍ K₁.action

  cf₁ : CoreFree 𝒰  (WreathProduct.Diag≀ 𝒮 K₁.action)
                    (WreathProduct.Diag≀-isSubgroup 𝒮 K₁.action)
  cf₁ = wreath-coreFree k₁ nc cf

  -- Second application: a core-free representation of 𝑳″ = 𝑳 on 𝒮 ≀ 𝒰.
  k₂ : WreathIntervalData 𝒮 (dualLattice 𝑳) 𝒰
        (WreathProduct.Diag≀ 𝒮 K₁.action)
        (WreathProduct.Diag≀-isSubgroup 𝒮 K₁.action)
  k₂ = kwi (dualLattice 𝑳) 𝒰
        (WreathProduct.Diag≀ 𝒮 K₁.action)
        (WreathProduct.Diag≀-isSubgroup 𝒮 K₁.action)
        K₁.finite cf₁ K₁.interval (nontrivial-dual 𝑳 two)

  module K₂ = WreathIntervalData k₂

  cf₂ : CoreFree (𝒮 ≀ᵍ K₂.action)
                 (WreathProduct.Diag≀ 𝒮 K₂.action)
                 (WreathProduct.Diag≀-isSubgroup 𝒮 K₂.action)
  cf₂ = wreath-coreFree k₂ nc cf₁

  -- The double dual is definitionally 𝑳 at the order level, so cf-IE applies.
  P-holds : P (𝒮 ≀ᵍ K₂.action)
  P-holds = cf-ie  (𝒮 ≀ᵍ K₂.action)
                   (WreathProduct.Diag≀ 𝒮 K₂.action)
                   (WreathProduct.Diag≀-isSubgroup 𝒮 K₂.action)
                   cf₂ K₂.interval
```

#### The omission corollary

**The form the RP-2 catalog quotes**: a property with **no** wreath products over
some admissible `𝒮` cannot be cf-IE via a lattice with a core-free representation
and two distinct elements.  Classically: solvability, being alternating or
symmetric, and almost simplicity all omit `S ≀ Ū` for suitable simple `S`, so none
of them is cf-IE by a group-representable lattice.

```agda
omits-wreaths→not-cfIE :
  ∀ {ℓP} (P : GroupProperty ℓP) (𝑳 : Lattice) (𝒮 : Group 0ℓ 0ℓ)
  → NontrivialCenterless 𝒮
  → KurzweilWreathInterval 𝒮
  → (∀ (𝒰 : Group 0ℓ 0ℓ) (m : ℕ) (A : RightAction (Fin (2 + m)) 𝒰) → ¬ P (𝒮 ≀ᵍ A))
  → cfIE P 𝑳
  → (r : CoreFreeRepresentable 𝑳)
  → FiniteAlgebra (proj₁ (CoreFreeRepresentable.rep r .grp))
  → Nontrivial 𝑳
  → ⊥
omits-wreaths→not-cfIE P 𝑳 𝒮 nc kwi omits cf-ie r fin two = omits 𝒰 m A holds
  where
  found : ∃[ 𝒰 ] ∃[ m ] Σ[ A ∈ RightAction (Fin (2 + m)) 𝒰 ] P (𝒮 ≀ᵍ A)
  found = cfIE-must-have-wreaths P 𝑳 𝒮 nc kwi cf-ie r fin two

  𝒰 : Group 0ℓ 0ℓ
  𝒰 = found .proj₁

  m : ℕ
  m = found .proj₂ .proj₁

  A : RightAction (Fin (2 + m)) 𝒰
  A = found .proj₂ .proj₂ .proj₁

  holds : P (𝒮 ≀ᵍ A)
  holds = found .proj₂ .proj₂ .proj₂
```

#### The dead-end question, and what Lemma 3.3 says about it

RP-4's question is the `n = 2` case of the empty-intersection hunt of RP-3, where
the two classes are a property and its negation; it is *stated* here, in the
vacuity-disciplined form (each lattice comes with a core-free representation), and
deliberately not asserted: no inhabitant is claimed in either direction.

```agda
-- A type representing the dead-end assertion: a property and its negation
-- cannot both be cf-IE via lattices with core-free representations.
cfIE-no-contradictory-Statement : (ℓP : Level) → Type (lsuc 0ℓ ⊔ lsuc ℓP)
cfIE-no-contradictory-Statement ℓP =
  ∀ (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : Lattice)
  → CoreFreeRepresentable 𝑳₁ → cfIE P 𝑳₁
  → CoreFreeRepresentable 𝑳₂ → cfIE (λ 𝒢 → ¬ P 𝒢) 𝑳₂
  → ⊥
```

**What Lemma 3.3 settles**.
A contradictory pair would have to be **jointly wreath-rich**; both classes
contain wreath products over every admissible `𝒮`.  So the note's no-go for plain
IE (Lemma 3.2, whose fattening argument destroys core-freeness) cannot be replayed
here, and any refutation must separate the two classes by invariants finer than
wreath content: the unique minimal normal subgroup, its centralizer, and the
permutation action on it that RP-1's Lemma 3.7 provides for parachute
representations.

```agda
-- A contradictory cf-IE pair is jointly wreath-rich over every admissible 𝒮.
contradictory-pair-wreaths :
  ∀ {ℓP} (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : Lattice) (𝒮 : Group 0ℓ 0ℓ)
  → NontrivialCenterless 𝒮
  → KurzweilWreathInterval 𝒮
  → cfIE P 𝑳₁
  → (r₁ : CoreFreeRepresentable 𝑳₁)
  → FiniteAlgebra (proj₁ (CoreFreeRepresentable.rep r₁ .grp))
  → Nontrivial 𝑳₁
  → cfIE (λ 𝒢 → ¬ P 𝒢) 𝑳₂
  → (r₂ : CoreFreeRepresentable 𝑳₂)
  → FiniteAlgebra (proj₁ (CoreFreeRepresentable.rep r₂ .grp))
  → Nontrivial 𝑳₂
  →  (∃[ 𝒰 ] ∃[ m ] Σ[ A ∈ RightAction (Fin (2 + m)) 𝒰 ] P (𝒮 ≀ᵍ A))
     × (∃[ 𝒱 ] ∃[ l ] Σ[ B ∈ RightAction (Fin (2 + l)) 𝒱 ] ¬ P (𝒮 ≀ᵍ B))
contradictory-pair-wreaths P 𝑳₁ 𝑳₂ 𝒮 nc kwi cf-ie₁ r₁ fin₁ two₁ cf-ie₂ r₂ fin₂ two₂ =
    cfIE-must-have-wreaths P 𝑳₁ 𝒮 nc kwi cf-ie₁ r₁ fin₁ two₁
  , cfIE-must-have-wreaths (λ 𝒢 → ¬ P 𝒢) 𝑳₂ 𝒮 nc kwi cf-ie₂ r₂ fin₂ two₂
```

**The reduction that places the question in the program's chain**.

The parachute statement (C) of [FLRP.Enforceable][], for families of *finite*
lattices with two big canopies, *implies* there is no contradictory pair, by
instantiating the family at `(𝑳₁ , 𝑳₂)` with properties `(P , ¬ P)`; the single
group statement (C) produces would satisfy both.  Contrapositively, a
contradictory pair refutes (C), hence, through the RP-1 meta-theorem and the
Pálfy–Pudlák entry, the FLRP itself.  This is the formal content of "the dead-end
question sits below statement (C)"; what stands between the two formulations is
the finite-presentation transport recorded as open in the RP-1 design note, plus
(C)'s three-element side conditions.

```agda
-- Statement (C) leaves no room for a contradictory pair on big finite lattices.
statement-C→no-contradictory-pair :
  ∀ {ℓP} → Statement-C ℓP
  → (P : GroupProperty ℓP) (𝑳₁ 𝑳₂ : FiniteLattice)
  → HasThreeDistinct (toLattice 𝑳₁) → HasThreeDistinct (toLattice 𝑳₂)
  → cfIE P (toLattice 𝑳₁) → cfIE (λ 𝒢 → ¬ P 𝒢) (toLattice 𝑳₂)
  → ⊥
statement-C→no-contradictory-pair {ℓP} stC P 𝑳₁ 𝑳₂ three₁ three₂ cf-ie₁ cf-ie₂ =
  (Ps-hold 1F) (Ps-hold 0F)
  where
  family : Fin 2 → FiniteLattice
  family 0F = 𝑳₁
  family 1F = 𝑳₂

  Ps : Fin 2 → GroupProperty ℓP
  Ps 0F = P
  Ps 1F = λ 𝒢 → ¬ P 𝒢

  two-all : ∀ i → Nontrivial (toLattice (family i))
  two-all 0F = threeDistinct→nontrivial (toLattice 𝑳₁) three₁
  two-all 1F = threeDistinct→nontrivial (toLattice 𝑳₂) three₂

  two-big : TwoBigCanopies family
  two-big = 0F , 1F , (λ ()) , three₁ , three₂

  cfs : ∀ i → cfIE (Ps i) (toLattice (family i))
  cfs 0F = cf-ie₁
  cfs 1F = cf-ie₂

  joint :
    ∃[ 𝒢 ]
      (∀ i → Ps i 𝒢)
      × ( ∀ i → ∃[ H ] ∃[ H-sg ] (  CoreFree 𝒢 H H-sg
                                    × IntervalIso 𝒢 H H-sg (toLattice (family i)) ) )
  joint = stC 0 family Ps two-all two-big cfs

  Ps-hold : ∀ i → Ps i (joint .proj₁)
  Ps-hold = joint .proj₂ .proj₁
```

--------------------------------------

[^1]: arXiv:1205.1927 ("the note"), vendored at `docs/papers/flrp/ieprops/`;
      Lemma 3.3 (`lem:IE-must-have-wreaths`) and its proof, which cites the
      two interval facts to H. Kurzweil, *Endliche Gruppen mit vielen
      Untergruppen*, J. reine angew. Math. 356 (1985) 140–160.  The design
      note for this phase is `docs/notes/flrp-rp4-wreath.md`.
