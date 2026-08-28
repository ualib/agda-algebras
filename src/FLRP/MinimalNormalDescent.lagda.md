---
layout: default
file: "src/FLRP/MinimalNormalDescent.lagda.md"
title: "FLRP.MinimalNormalDescent module (The Agda Universal Algebra Library)"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Minimal normal subgroups exist, by well-founded descent

This is the [FLRP.MinimalNormalDescent][] module of the [Agda Universal Algebra Library][].

It proves the last finiteness gap of the parachute structure theory:

> **every nontrivial normal subgroup of a finite group contains a minimal one.**

RP-1 ([FLRP.Parachute][]) threads this as the module parameter `M` of
`Structure.Minimal`{.AgdaModule}, and RP-2 ([FLRP.Reductions][]) threads it as the
antecedent `MinimalNormalDescent`{.AgdaFunction} of the enforced property in catalog
Entries 1–3 (`docs/notes/flrp-rp1-parachutes.md` § 4,
`docs/notes/flrp-rp2-catalog.md` § 4.2).  Here it becomes a theorem.

#### The argument, and why it is stated at Layer D

The proof is well-founded descent on a **measure**.  A `FiniteAlgebra`{.AgdaRecord}
([Setoid.Algebras.Finite][]) supplies a surjective enumeration `enum : Fin card → G`
of the carrier and a decision procedure for its setoid equality.  From these the
number of *enumerated indices* that land inside a subgroup — `measure`{.AgdaFunction}
below — is a natural number, and it **strictly decreases** under proper inclusion of
equality-respecting subgroups: if `A ⊆ B` and some element of `B` is outside `A`,
then, pulling that element back through `enum`, `B` occupies an index `A` does not, so
`measure A < measure B` (`measure-strict`{.AgdaFunction}).  A strictly decreasing chain
of `ℕ`-measures terminates, which is `<`-well-foundedness of `Data.Nat.Induction`; the
terminal member of such a chain is minimal.

Two points fix the *shape* of the statement, both forced by the ADR-008 two-layer
discipline (`docs/adr/008-two-layer-congruence-discipline.md`).

+  **Membership must be decidable (Layer D)**.  A measure counts enumerated elements,
   so it needs to *decide* membership.  A merely semantic subgroup predicate
   `Pred G 0ℓ` has no computable order — deciding "is `enum i` inside?" is exactly the
   oracle content ADR-008 isolates — so every subgroup we quantify over is presented
   with a decision procedure, packaged as `NSGᵈ`{.AgdaRecord}.  This mirrors
   `DecCon`{.AgdaFunction} next to `Con`{.AgdaFunction}, and `Intervalᵈ`{.AgdaFunction}
   of [FLRP.Enforceable][] next to `Interval≈`{.AgdaFunction}.

+  **Finding a smaller subgroup needs an enumeration of them**.  Descent must, at each
   step, either exhibit a strictly smaller nontrivial normal subgroup or certify that
   none exists.  Certifying a negative over *all* subgroups is a finite search only
   against a **complete list** of the (Layer-D) normal subgroups —
   `CompleteNSGᵈ`{.AgdaRecord} — the group-side analogue of
   `FiniteCongruencesᵈ`{.AgdaRecord} ([Setoid.Congruences.Finite.Decidable][]).  It is
   honest finiteness data (never a minimality assumption), inhabited for concrete
   groups by computation exactly as the congruence certificates are.

The result is `minimalNormalᵈ`{.AgdaFunction}: from a `FiniteAlgebra`{.AgdaRecord} and a
`CompleteNSGᵈ`{.AgdaRecord}, every nontrivial `NSGᵈ`{.AgdaRecord} `N` contains a
`IsMinimalᵈ`{.AgdaRecord} `M` — minimal among the Layer-D normal subgroups, with no
postulate and no classical axiom.

#### Bridging to the semantic consumer

The catalog's `MinimalNormalDescent`{.AgdaFunction} and RP-1's `IsMinimalNormal`{.AgdaRecord}
([Classical.Structures.Group.MinimalNormal][]) quantify over *semantic* normal
subgroups.  Crossing from the Layer-D theorem to that semantic form is the one place a
classical ingredient is needed, and it is named, not smuggled:
`AllNormalDecidable`{.AgdaFunction} — every normal subgroup of the group has decidable
membership.  Under it (and the finiteness data), `minimalNormalDescent`{.AgdaFunction}
discharges the catalog's property verbatim.  For a concrete finite group the
hypothesis holds by computation; in general it is the same seam between Layer S and
Layer D that ADR-008 accounts for, so it is exposed as an explicit hypothesis rather
than proved here.  Wiring this into [FLRP.Reductions][] — dropping the antecedent from
Entries 1–3 — is deferred (issue #510, stretch goal).

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.MinimalNormalDescent where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                          using  ( Bool ; true ; false )
open import Data.Bool.Properties                    using  () renaming ( _≟_ to _≟ᵇ_ )
open import Data.Empty                              using  ( ⊥-elim )
open import Data.Fin.Base                           using  ( Fin ; zero ; suc )
open import Data.Fin.Properties                     using  ( all? ; any? )
open import Data.List.Base                          using  ( List )
open import Data.List.Membership.Propositional      using  () renaming ( _∈_ to _∈ˡ_ )
open import Data.List.Relation.Unary.All            using  ( All ) renaming ( lookup to all-lookup )
open import Data.List.Relation.Unary.All.Properties using  ( ¬Any⇒All¬ )
open import Data.List.Relation.Unary.Any            using  ( Any ; satisfied ) renaming ( any? to anyᴸ? )
open import Data.Nat.Base                           using  ( ℕ ; zero ; suc ; _+_ ; _<_ ; _≤_ ; s≤s ; z≤n )
open import Data.Nat.Induction                      using  ( <-wellFounded ; Acc ; acc )
open import Data.Nat.Properties                     using  ( +-mono-≤ ; +-mono-<-≤ ; +-mono-≤-< )
open import Data.Product                            using  ( _×_ ; _,_ ; Σ-syntax ; ∃-syntax ; proj₁ ; proj₂ )
open import Level                                   using  ( Level ; 0ℓ ) renaming ( suc to lsuc )
open import Relation.Binary                         using  ( Setoid )
open import Relation.Binary.PropositionalEquality   using  ( _≡_ ; refl )
open import Relation.Nullary                        using  ( ¬_ )
open import Relation.Nullary.Decidable.Core         using  ( Dec ; yes ; no ; does ; _×-dec_ ; _→-dec_
                                                           ; ¬? ; map′ ; decidable-stable )
open import Relation.Nullary.Decidable              using  ( dec-true ; dec-false )
open import Relation.Unary                          using  ( Pred ; _∈_ ; _⊆_ ; _≐_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Group  using  ( Group ; module Group-Op ; IsSubgroup
                                               ; module Conjugate ; trivialSubgroup
                                               ; module MinimalNormal )
open import Setoid.Algebras             using  ( 𝕌[_] ; 𝔻[_] ; FiniteAlgebra )
```
-->

#### A counting measure on `Fin`-indexed Boolean predicates

`count`{.AgdaFunction} tallies the indices a Boolean-valued function marks `true`.  It
is monotone under pointwise implication (`count-mono`{.AgdaFunction}) and *strictly*
monotone once a single index flips from `false` to `true` (`count-strict`{.AgdaFunction});
these two facts are the whole finiteness content of the descent, isolated from the
group theory.

```agda
private
  b2n : Bool → ℕ
  b2n true   = 1
  b2n false  = 0

  count : ∀ {n} → (Fin n → Bool) → ℕ
  count {zero}   f = 0
  count {suc n}  f = b2n (f zero) + count (λ i → f (suc i))

  b2n-mono : (a b : Bool) → (a ≡ true → b ≡ true) → b2n a ≤ b2n b
  b2n-mono false  b      _ = z≤n
  b2n-mono true   true   _ = s≤s z≤n
  b2n-mono true   false  h with h refl
  ... | ()

  b2n-strict : (a b : Bool) → a ≡ false → b ≡ true → b2n a < b2n b
  b2n-strict false true   _ _ = s≤s z≤n
  b2n-strict true  _      ()
  b2n-strict false false  _ ()

  count-mono : ∀ {n} (f g : Fin n → Bool)
    → (∀ i → f i ≡ true → g i ≡ true) → count f ≤ count g
  count-mono {zero}   f g h = z≤n
  count-mono {suc n}  f g h =
    +-mono-≤ (b2n-mono (f zero) (g zero) (h zero))
             (count-mono (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

  count-strict : ∀ {n} (f g : Fin n → Bool)
    → (∀ i → f i ≡ true → g i ≡ true)
    → (j : Fin n) → f j ≡ false → g j ≡ true → count f < count g
  count-strict {zero}   _ _ _ ()
  count-strict {suc n}  f g h zero     fj gj =
    +-mono-<-≤ (b2n-strict (f zero) (g zero) fj gj)
               (count-mono (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))
  count-strict {suc n}  f g h (suc j)  fj gj =
    +-mono-≤-< (b2n-mono (f zero) (g zero) (h zero))
               (count-strict (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)) j fj gj)
```

Two small decidability helpers: recover the proof behind a `true` decision, and the
refutation behind a `false` one, and turn a `Bool` that is not `false` into `true`.

```agda
private
  fromTrue : ∀ {ℓ} {P : Type ℓ} (d : Dec P) → does d ≡ true → P
  fromTrue (yes p)  _ = p
  fromTrue (no _)   ()

  fromFalse : ∀ {ℓ} {P : Type ℓ} (d : Dec P) → does d ≡ false → ¬ P
  fromFalse (no ¬p)  _ = ¬p
  fromFalse (yes _)  ()

  ≢false→≡true : (b : Bool) → ¬ (b ≡ false) → b ≡ true
  ≢false→≡true true   _  = refl
  ≢false→≡true false  ¬p = ⊥-elim (¬p refl)
```

#### The descent, over one finite group

Throughout, `𝒢`{.AgdaBound} is a group whose underlying algebra carries a
`FiniteAlgebra`{.AgdaRecord} witness `𝑭`{.AgdaBound}.  Subgroup predicates live at the
level `L = 0ℓ` of the subgroup lattice, as everywhere in the FLRP program.

```agda
module _ (𝒢 : Group 0ℓ 0ℓ) (𝑭 : FiniteAlgebra (proj₁ 𝒢)) where
  private
    𝑮 = proj₁ 𝒢
    G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using  ( _≈_ ) renaming ( sym to ≈sym )
  open Group-Op 𝒢     using  ( ε )
  open Conjugate 𝒢    using  ( IsNormal ; trivialSubgroupIsnormal )
  open MinimalNormal 𝒢 0ℓ
  open FiniteAlgebra 𝑭  using  ( card ; enum ; enum-sur ) renaming ( _≟_ to _≟ᴳ_ )
```

A **Layer-D normal subgroup** bundles a normal subgroup with a decision procedure for
its membership.

```agda
  record NSGᵈ : Type (lsuc 0ℓ) where
    constructor mkNSGᵈ
    field
      pred  : Pred G 0ℓ
      nsg   : IsNormalSubgroup pred
      mem?  : ∀ x → Dec (x ∈ pred)
  open NSGᵈ public

  -- The membership predicate of a subgroup respects the setoid equality.
  private
    respOf : (A : NSGᵈ) {x y : G} → x ≈ y → x ∈ pred A → y ∈ pred A
    respOf A = IsSubgroup.respects (isSubgroup (nsg A))
```

The measure of a Layer-D subgroup: how many enumerated indices land inside it.

```agda
  measure : NSGᵈ → ℕ
  measure A = count (λ i → does (mem? A (enum i)))
```

**Decidable inclusion.**  `A ⊆ B` between two Layer-D subgroups is decidable, because
on the finite carrier it is equivalent to the pointwise Boolean implication over the
`card` enumerated indices.  The forward direction pulls an arbitrary element back to an
index through `enum-sur`; the backward direction reads inclusion off at each index.

```agda
  private
    IncBits : NSGᵈ → NSGᵈ → Type 0ℓ
    IncBits A B = ∀ i → does (mem? A (enum i)) ≡ true → does (mem? B (enum i)) ≡ true

    incbits→⊆ : (A B : NSGᵈ) → IncBits A B → pred A ⊆ pred B
    incbits→⊆ A B bm {x} x∈A =
      respOf B ei≈x (fromTrue (mem? B (enum ix))
        (bm ix (dec-true (mem? A (enum ix)) (respOf A (≈sym ei≈x) x∈A))))
      where
      ix    = proj₁ (enum-sur x)
      ei≈x  = proj₂ (enum-sur x)

    ⊆→incbits : (A B : NSGᵈ) → pred A ⊆ pred B → IncBits A B
    ⊆→incbits A B A⊆B i eq =
      dec-true (mem? B (enum i)) (A⊆B (fromTrue (mem? A (enum i)) eq))

  _⊆ᵈ?_ : (A B : NSGᵈ) → Dec (pred A ⊆ pred B)
  A ⊆ᵈ? B = map′ (incbits→⊆ A B) (⊆→incbits A B) incbits?
    where
    incbits? : Dec (IncBits A B)
    incbits? = all? (λ i → (does (mem? A (enum i)) ≟ᵇ true)
                     →-dec (does (mem? B (enum i)) ≟ᵇ true))
```

When inclusion **fails**, a finite search produces the witnessing element — the point
where Layer-D presentation buys a constructive witness that the negated semantic
inclusion `¬ (A ⊆ B)` cannot give on its own.

```agda
  private
    ¬⊆→witness : (A B : NSGᵈ) → ¬ (pred A ⊆ pred B)
      → Σ[ w ∈ G ] (w ∈ pred A) × (¬ (w ∈ pred B))
    ¬⊆→witness A B ¬A⊆B
      with any? (λ i → (does (mem? A (enum i)) ≟ᵇ true)
                 ×-dec (does (mem? B (enum i)) ≟ᵇ false))
    ... | yes (i , eqA , eqB) =
            enum i , fromTrue (mem? A (enum i)) eqA , fromFalse (mem? B (enum i)) eqB
    ... | no ¬ex = ⊥-elim (¬A⊆B (incbits→⊆ A B incbits))
      where
      incbits : IncBits A B
      incbits i eqA = ≢false→≡true (does (mem? B (enum i))) (λ eqf → ¬ex (i , eqA , eqf))
```

**Strict monotonicity of the measure.**  If `A ⊆ B` and some `w ∈ B` is outside `A`,
the index of `w` is inside `B` but not `A`, so `count` strictly increases.

```agda
  measure-strict : (A B : NSGᵈ) → pred A ⊆ pred B
    → (w : G) → w ∈ pred B → ¬ (w ∈ pred A) → measure A < measure B
  measure-strict A B A⊆B w w∈B w∉A =
    count-strict (λ i → does (mem? A (enum i))) (λ i → does (mem? B (enum i)))
                 bitmono ix fA≡false fB≡true
    where
    ix    = proj₁ (enum-sur w)
    ei≈w  = proj₂ (enum-sur w)
    bitmono : ∀ i → does (mem? A (enum i)) ≡ true → does (mem? B (enum i)) ≡ true
    bitmono i eq = dec-true (mem? B (enum i)) (A⊆B (fromTrue (mem? A (enum i)) eq))
    fB≡true : does (mem? B (enum ix)) ≡ true
    fB≡true = dec-true (mem? B (enum ix)) (respOf B (≈sym ei≈w) w∈B)
    fA≡false : does (mem? A (enum ix)) ≡ false
    fA≡false = dec-false (mem? A (enum ix)) (λ ei∈A → w∉A (respOf A ei≈w ei∈A))
```

**Layer-D minimality.**  `M` is minimal among the Layer-D normal subgroups: nontrivial,
normal, decidably presented, and below every nontrivial Layer-D normal subgroup it
contains.

```agda
  record IsMinimalᵈ (M : Pred G 0ℓ) : Type (lsuc 0ℓ) where
    field
      memberᵈ?     : ∀ x → Dec (x ∈ M)
      normalᵈ      : IsNormalSubgroup M
      nontrivialᵈ  : Nontrivial M
      minimalᵈ     : (N : Pred G 0ℓ) → IsNormalSubgroup N → (∀ x → Dec (x ∈ N))
                   → N ⊆ M → Nontrivial N → M ⊆ N
```

The trivial subgroup as Layer-D data — its membership is the identity test — so that
nontriviality of a candidate is a decidable inclusion into it.

```agda
  private
    Trivᵈ : NSGᵈ
    Trivᵈ = mkNSGᵈ Triv
                   (record  { isSubgroup  = proj₂ (trivialSubgroup 𝒢)
                            ; isNormal    = trivialSubgroupIsnormal })
                   (λ x → x ≟ᴳ ε)
```

`Smaller M₀ e` says the listed subgroup `e` is a *proper* nontrivial normal subgroup
below `M₀`; it is decidable, so the search for one is a decidable `Any` over the list.

```agda
  private
    Smaller : NSGᵈ → NSGᵈ → Type 0ℓ
    Smaller M₀ e = (pred e ⊆ pred M₀) × (Nontrivial (pred e) × ¬ (pred M₀ ⊆ pred e))

    Smaller? : (M₀ e : NSGᵈ) → Dec (Smaller M₀ e)
    Smaller? M₀ e = (e ⊆ᵈ? M₀) ×-dec (¬? (e ⊆ᵈ? Trivᵈ) ×-dec ¬? (M₀ ⊆ᵈ? e))
```

**The finiteness interface.**  A finite list of the Layer-D normal subgroups, complete
up to `≐`: every Layer-D normal subgroup equals a listed one (as sets).

```agda
  record CompleteNSGᵈ : Type (lsuc 0ℓ) where
    field
      nsgs      : List NSGᵈ
      complete  : (N : NSGᵈ) → Σ[ e ∈ NSGᵈ ] (e ∈ˡ nsgs) × (pred N ≐ pred e)
```

**The theorem.**  Well-founded descent on `measure`.  Given a nontrivial `M₀`, search
the complete list for a proper nontrivial normal subgroup below it.  If one is found,
its measure is strictly smaller, so the recursion continues into it; if none is found,
`M₀` is already minimal, because completeness turns any nontrivial Layer-D normal
subgroup below `M₀` into a listed one, and the failed search forces `M₀` beneath it.

```agda
  module _ (𝑪 : CompleteNSGᵈ) where
    open CompleteNSGᵈ 𝑪

    private
      descend : (M₀ : NSGᵈ) → Nontrivial (pred M₀) → Acc _<_ (measure M₀)
        → Σ[ M ∈ Pred G 0ℓ ] (IsMinimalᵈ M × (M ⊆ pred M₀))
      descend M₀ nt (acc rs) with anyᴸ? (Smaller? M₀) nsgs
      ... | yes found =
              let (e , e⊆M₀ , e-nt , ¬M₀⊆e) = satisfied found
                  (w , w∈M₀ , w∉e)          = ¬⊆→witness M₀ e ¬M₀⊆e
                  (M , M-min , M⊆e)         =
                    descend e e-nt (rs (measure-strict e M₀ e⊆M₀ w w∈M₀ w∉e))
              in M , M-min , λ x∈M → e⊆M₀ (M⊆e x∈M)
      ... | no ¬found =
              pred M₀ , record  { memberᵈ?     = mem? M₀
                                ; normalᵈ      = nsg M₀
                                ; nontrivialᵈ  = nt
                                ; minimalᵈ     = M₀-least } , λ x∈M₀ → x∈M₀
        where
        all¬ : All (λ e → ¬ Smaller M₀ e) nsgs
        all¬ = ¬Any⇒All¬ nsgs ¬found

        M₀-least : (N : Pred G 0ℓ) → IsNormalSubgroup N → (∀ x → Dec (x ∈ N))
              → N ⊆ pred M₀ → Nontrivial N → pred M₀ ⊆ N
        M₀-least N N-nsg N? N⊆M₀ N-nt x∈M₀ = e⊆N (M₀⊆e x∈M₀)
          where
          Nᵈ : NSGᵈ
          Nᵈ = mkNSGᵈ N N-nsg N?
          e     = proj₁ (complete Nᵈ)
          e∈    = proj₁ (proj₂ (complete Nᵈ))
          N≐e   = proj₂ (proj₂ (complete Nᵈ))
          N⊆e   = proj₁ N≐e
          e⊆N   = proj₂ N≐e
          e⊆M₀  : pred e ⊆ pred M₀
          e⊆M₀ x∈e = N⊆M₀ (e⊆N x∈e)
          e-nt  : Nontrivial (pred e)
          e-nt e⊆Triv = N-nt (λ x∈N → e⊆Triv (N⊆e x∈N))
          M₀⊆e  : pred M₀ ⊆ pred e
          M₀⊆e  = decidable-stable (M₀ ⊆ᵈ? e)
                    (λ ¬M₀⊆e → all-lookup all¬ e∈ (e⊆M₀ , e-nt , ¬M₀⊆e))

    minimalNormalᵈ : (N : NSGᵈ) → Nontrivial (pred N)
      → Σ[ M ∈ Pred G 0ℓ ] (IsMinimalᵈ M × (M ⊆ pred N))
    minimalNormalᵈ N nt = descend N nt (<-wellFounded (measure N))
```

#### Bridge to the semantic consumer

`AllNormalDecidable`{.AgdaFunction} — every normal subgroup has decidable membership —
is the named classical ingredient (ADR-008's Layer S / Layer D seam).  Under it, a
Layer-D minimal normal subgroup is a *semantic* one: the semantic `minimal`{.AgdaField}
query supplies its own decision procedure through the hypothesis.

```agda
  AllNormalDecidable : Type (lsuc 0ℓ)
  AllNormalDecidable = (N : Pred G 0ℓ) → IsNormalSubgroup N → (∀ x → Dec (x ∈ N))

  IsMinimalᵈ→IsMinimalNormal : AllNormalDecidable → {M : Pred G 0ℓ}
    → IsMinimalᵈ M → IsMinimalNormal M
  IsMinimalᵈ→IsMinimalNormal allDec mᵈ = record
    { normalSubgroup  = IsMinimalᵈ.normalᵈ mᵈ
    ; nontrivial      = IsMinimalᵈ.nontrivialᵈ mᵈ
    ; minimal         = λ N N-nsg N⊆M N-nt →
                          IsMinimalᵈ.minimalᵈ mᵈ N N-nsg (allDec N N-nsg) N⊆M N-nt }
```

Assembling the two: the finiteness data and `AllNormalDecidable`{.AgdaFunction} together
discharge the catalog's `MinimalNormalDescent`{.AgdaFunction} — every nontrivial
semantic normal subgroup contains a semantic minimal one — for a finite group.

```agda
  module _ (𝑪 : CompleteNSGᵈ) (allDec : AllNormalDecidable) where

    minimalNormalDescent : (N : Pred G 0ℓ) → IsNormalSubgroup N → Nontrivial N
      → Σ[ M ∈ Pred G 0ℓ ] (IsMinimalNormal M × (M ⊆ N))
    minimalNormalDescent N N-nsg N-nt =
      let (M , M-minᵈ , M⊆N) = minimalNormalᵈ 𝑪 (mkNSGᵈ N N-nsg (allDec N N-nsg)) N-nt
      in M , IsMinimalᵈ→IsMinimalNormal allDec M-minᵈ , M⊆N
```

---

The statement `minimalNormalᵈ`{.AgdaFunction} is the honest Layer-D theorem; the
`FiniteAlgebra`{.AgdaRecord} measure is its finiteness core, and
`CompleteNSGᵈ`{.AgdaRecord} the finite normal-subgroup data it searches.  Deriving that
list from `FiniteAlgebra`{.AgdaRecord} alone (by enumerating candidate subsets and
testing the subgroup axioms, the group-side of `allDecCons`{.AgdaFunction}), and wiring
`minimalNormalDescent`{.AgdaFunction} into the Entries 1–3 of [FLRP.Reductions][], are
the remaining steps of issue #510.
