---
layout: default
file: "src/Setoid/Subalgebras/Subdirect/Finite.lagda.md"
title: "Setoid.Subalgebras.Subdirect.Finite module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Finite Birkhoff: a constructive subdirect SI-representation

This is the [Setoid.Subalgebras.Subdirect.Finite][] module of the [Agda Universal Algebra Library][].

[Setoid.Subalgebras.Subdirect.BirkhoffSI][] proved the *choice-free core* of
Birkhoff's subdirect representation theorem and stated the general theorem
`Birkhoff-subdirect` *relative to* the choice principle `SubdirectSIRep 𝑨` — the
existence, for every algebra, of a separating family of congruences whose quotients
are subdirectly irreducible.

Producing that family for an arbitrary algebra is a Zorn's-lemma step (a congruence
maximal among those excluding a given pair), which is incompatible with a
postulate-free formalization in constructive type theory.

This module discharges that parameter for a class of *finite* algebras: it constructs
`SubdirectSIRep 𝑨` outright, with no choice and no postulate, and feeds it to the
choice-free reduction `SIRep→Representable`.[^1]

#### What "finite" must mean here

The classical proof selects, for each pair `a ≢ b`, a congruence *maximal* among
those not relating `a` and `b`; such a congruence is completely meet-irreducible, so
its quotient is subdirectly irreducible.  To find that maximal congruence by a
*search* we must enumerate the congruence lattice, and to recognise subdirect
irreducibility (whose monolith condition quantifies over all congruences of the
quotient) the enumeration must be complete — every congruence must equal a listed
one, up to mutual containment (denote here `≑`).

Crucially, carrier-finiteness along with decidable setoid equality do not, by
themselves, admit such an enumeration constructively (see
[Setoid.Congruences.Finite][] for the counterexample), so the finiteness data comes
through two independent interfaces.

1.  `FiniteAlgebra`{.AgdaRecord}, from [Setoid.Algebras.Finite][]: decidable `≈` and
    a finite surjective enumeration of the carrier, used here to count the pairs a
    congruence relates;
2.  `FiniteCongruences`{.AgdaRecord}, from [Setoid.Congruences.Finite][]: a finite
    list of *decidable* congruences (`DecCon`{.AgdaFunction}), complete up to `≑` —
    the searchable congruence lattice.

Everything downstream is then fully constructive and computes.  Classically every
finite algebra furnishes both witnesses, so `finite-Birkhoff` is Birkhoff's theorem
for finite algebras; the two records are precisely the constructive data that make
the search go through under `--safe` Agda.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect.Finite {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                 using  () renaming ( Set to Type )
open import Data.Empty                     using  ( ⊥-elim )
open import Data.Fin.Base                  using  ( Fin )
open import Data.Fin.Properties            using  ( all? ; ¬∀⟶∃¬ )
open import Data.List.Base                 using  ( List ; [] ; _∷_ ; filter ; length
                                                  ; allFin ; cartesianProduct )
open import Data.List.Extrema.Nat          using  ( argmax ; f[xs]≤f[argmax] ; argmax-sel )
open import Data.List.Relation.Unary.All   using  ( lookup )
open import Data.List.Relation.Unary.Any   using  ( here ; there )
open import Data.Nat.Base                  using  ( ℕ ; _≤_ ; _<_ ; z≤n ; s≤s )
open import Data.Nat.Properties            using  ( m≤n⇒m≤1+n ; n<1+n ; <-trans
                                                  ; ≤-<-trans ; n≮n )
open import Data.Product                   using  ( _×_ ; _,_ ; Σ-syntax ; proj₁ ; proj₂ )
open import Data.Sum.Base                  using  ( inj₁ ; inj₂ )
open import Level                          using  ( Level ; _⊔_ ; 0ℓ ; lower )
open import Relation.Binary                using  ( Setoid ; IsEquivalence )
open import Relation.Nullary               using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable     using  ( _→-dec_ ; ¬? )

open import Data.List.Membership.Propositional     using  ( _∈_ )
open import Relation.Binary.PropositionalEquality  using  ( _≡_ ; refl ; subst ; sym )

open import Data.List.Membership.Propositional.Properties
  using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-cartesianProduct⁺ ; ∈-allFin )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Basic        {𝑆 = 𝑆}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                using  ( FiniteAlgebra ; 𝟏
                                                         ; 𝟏-FiniteAlgebra )
open import Setoid.Congruences.Basic              using  ( Con ; mkcon ; is-equivalence ; _╱_
                                                         ; reflexive ; is-compatible ; 𝟘[_] )
open import Setoid.Congruences.Finite             using  ( ConRel ; 𝟏-FiniteCongruences
                                                         ; FiniteCongruences ; DecCon )

open import Setoid.Congruences.Generation         using  ( Cg ; Cg-least ; base )
open import Setoid.Congruences.Lattice   {𝑆 = 𝑆}  using  ( _⊆_ ; ⊆-trans )
open import Setoid.Congruences.Monolith  {𝑆 = 𝑆}  using  ( IsSubdirectlyIrreducible ; Nonzero
                                                         ; mono-nonzero ; mono-least )

open import Setoid.Subalgebras.Subdirect.Basic  {𝑆 = 𝑆}  using ( Separates )
open import Setoid.Subalgebras.Subdirect.BirkhoffSI {𝑆 = 𝑆}
  using (SubdirectSIRep; SubdirectlyRepresentable ; SIRep→Representable )

private variable α ρ : Level
```
-->

#### Two generic list lemmas

The maximal-congruence search is driven by counting, so we first record two
elementary, signature-agnostic facts about the length of a filtered list under two
decidable predicates `P ⊆ Q`: the count is monotone, and it is *strictly* smaller
whenever some listed element satisfies `Q` but not `P`.

```agda
private variable ℓ₁ ℓ₂ ℓ₃ : Level

private

  module _ {X : Type ℓ₁}{P : X → Type ℓ₂}{Q : X → Type ℓ₃}
           (P? : (x : X) → Dec (P x))(Q? : (x : X) → Dec (Q x))
           (sub : ∀ {x} → P x → Q x) where

    -- If P entails Q then no more elements pass the P-filter than the Q-filter.
    filter-length-mono : (xs : List X) → length (filter P? xs) ≤ length (filter Q? xs)
    filter-length-mono [] = z≤n
    filter-length-mono (x ∷ xs) with P? x | Q? x
    ... | yes _  | yes _  = s≤s (filter-length-mono xs)
    ... | yes px | no ¬qx = ⊥-elim (¬qx (sub px))
    ... | no _   | yes _  = m≤n⇒m≤1+n (filter-length-mono xs)
    ... | no _   | no _   = filter-length-mono xs

    -- If moreover some w ∈ xs has Q w and ¬ P w, the P-filter is strictly shorter.
    filter-length-strict : (xs : List X){w : X} → w ∈ xs → Q w → ¬ P w
                         → length (filter P? xs) < length (filter Q? xs)
    filter-length-strict (x ∷ xs) (here refl) qw ¬pw with P? x | Q? x
    ... | yes pw | _      = ⊥-elim (¬pw pw)
    ... | no _   | yes _  = s≤s (filter-length-mono xs)
    ... | no _   | no ¬qw = ⊥-elim (¬qw qw)
    filter-length-strict (x ∷ xs) (there w∈xs) qw ¬pw with P? x | Q? x
    ... | yes _  | yes _  = s≤s (filter-length-strict xs w∈xs qw ¬pw)
    ... | yes px | no ¬qx = ⊥-elim (¬qx (sub px))
    ... | no _   | yes _  = <-trans (filter-length-strict xs w∈xs qw ¬pw) (n<1+n _)
    ... | no _   | no _   = filter-length-strict xs w∈xs qw ¬pw

  -- From a decidable P and a refutation of (P → Q), recover P and ¬ Q.
  ¬→-split : {P : Type ℓ₁}{Q : Type ℓ₂} → Dec P → ¬ (P → Q) → P × ¬ Q
  ¬→-split (yes p) ¬pq = p , λ q → ¬pq (λ _ → q)
  ¬→-split (no ¬p) ¬pq = ⊥-elim (¬pq (λ p → ⊥-elim (¬p p)))
```

#### The construction

Fix an algebra `𝑨` equipped with both finiteness witnesses.  We abbreviate the
working congruence level as `ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ` — the absorbing level of
[Setoid.Congruences.Finite][], at which the generated (principal) congruences used
for the monolith stay put — and `pairs` is the list of all index pairs of the
carrier enumeration.

```agda
module _ {𝑨 : Algebra α ρ} (𝑭 : FiniteAlgebra 𝑨) (𝑪 : FiniteCongruences 𝑨) where
  open FiniteAlgebra 𝑭
  open FiniteCongruences 𝑪
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym )

  ℓ : Level
  ℓ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ

  pairs : List (Fin card × Fin card)
  pairs = cartesianProduct (allFin card) (allFin card)

  -- The decision procedure that a decidable congruence relates the i-th and j-th
  -- enumerated carrier elements, and the count of all such related index pairs.
  _∈?_ : ((i , j) : Fin card × Fin card)(d : DecCon 𝑨 ℓ)
       → Dec (ConRel d (enum i) (enum j))
  (i , j) ∈? d = proj₂ d (enum i) (enum j)

  count : DecCon 𝑨 ℓ → ℕ
  count d = length (filter (_∈? d) pairs)
```

A congruence contained in another relates no more pairs (`count-mono`); if the
containment is *proper on the enumerated carrier* it relates strictly fewer
(`count-strict`).  Both are instances of the generic list lemmas.

```agda
  count-mono : (d e : DecCon 𝑨 ℓ) → proj₁ d ⊆ proj₁ e → count d ≤ count e
  count-mono d e d⊆e = filter-length-mono (_∈? d) (_∈? e) (λ {p} → d⊆e) pairs

  count-strict : (d e : DecCon 𝑨 ℓ)(i j : Fin card)
    → proj₁ d ⊆ proj₁ e
    → ConRel e (enum i) (enum j)
    → ¬ ConRel d (enum i) (enum j)
    → count d < count e

  count-strict d e i j d⊆e eij ¬dij =
    filter-length-strict (_∈? d) (_∈? e) (λ {p} → d⊆e)
      pairs (∈-cartesianProduct⁺ (∈-allFin i) (∈-allFin j)) eij ¬dij
```

A relation that holds on every enumerated pair holds everywhere, because the
enumeration is surjective and congruences respect `≈`.  This lifts a carrier-level
containment to a genuine containment of congruences.

```agda
  carrier-lift : (R S : Con 𝑨 ℓ)
    → (∀ i j → proj₁ R (enum i) (enum j) → proj₁ S (enum i) (enum j))
    → R ⊆ S

  carrier-lift (R , pr) (S , ps) h {x} {y} Rxy =
    Strans (Srefl (≈sym ei≈x)) (Strans Sij (Srefl ej≈y))
    where
    open IsEquivalence (is-equivalence pr) using () renaming (trans to Rtrans)
    open IsEquivalence (is-equivalence ps) using () renaming (trans to Strans)

    Rrefl = reflexive pr
    Srefl = reflexive ps

    i j : Fin card
    i = proj₁ (enum-sur x)
    j = proj₁ (enum-sur y)

    ei≈x : enum i ≈ x
    ei≈x = proj₂ (enum-sur x)

    ej≈y : enum j ≈ y
    ej≈y = proj₂ (enum-sur y)

    Rij : R (enum i) (enum j)
    Rij = Rtrans (Rrefl ei≈x) (Rtrans Rxy (Rrefl (≈sym ej≈y)))

    Sij : S (enum i) (enum j)
    Sij = h i j Rij
```

Now fix a pair `a ≢ b`.  Among the congruences not relating `a` and `b` (a finite,
non-empty sublist of `cons`, non-empty because the diagonal is one) we pick one of
maximum `count`; `count`-maximality is `⊆`-maximality, by `count-mono`/`count-strict`.

```agda
  -- The diagonal (least) congruence at level ℓ, from Setoid.Congruences.Basic;
  -- its representative in `cons` witnesses the non-emptiness of `filtered` below.
  Δ : Con 𝑨 ℓ
  Δ = 𝟘[ 𝑨 ] {ℓ}

  module _ (a b : 𝕌[ 𝑨 ]) (a≢b : ¬ (a ≈ b)) where

    -- The congruences of `cons` that do not relate a and b.
    notRel? : (d : DecCon 𝑨 ℓ) → Dec (¬ ConRel d a b)
    notRel? d = ¬? (proj₂ d a b)

    a≢bCons : List (DecCon 𝑨 ℓ)
    a≢bCons = filter notRel? cons

    -- Of course the diagonal does not relate a and b, so it's in a≢bCons.
    ¬Δab : ¬ ConRel (witness Δ) a b
    ¬Δab Δab = a≢b (lower (proj₂ (witness≑ Δ) Δab))

    Δ∈a≢bCons : witness Δ ∈ a≢bCons
    Δ∈a≢bCons = ∈-filter⁺ notRel? (witness∈ Δ) ¬Δab

    -- The chosen congruence: a maximum-count member of `a≢bCons`.
    Θ-dec : DecCon 𝑨 ℓ
    Θ-dec = argmax count (witness Δ) a≢bCons

    Θ-dec∈filtered : Θ-dec ∈ a≢bCons
    Θ-dec∈filtered with argmax-sel count (witness Δ) a≢bCons
    ... | inj₁ eq = subst (_∈ a≢bCons) (sym eq) Δ∈a≢bCons
    ... | inj₂ ∈f = ∈f

    Θ : Con 𝑨 ℓ
    Θ = proj₁ Θ-dec

    ¬Θab : ¬ proj₁ Θ a b
    ¬Θab = proj₂ (∈-filter⁻ notRel? {xs = cons} Θ-dec∈filtered)

    -- count d ≤ count Θ for every member of `a≢bCons`: Θ has maximum count.
    Θ-max-count : (d : DecCon 𝑨 ℓ) → d ∈ a≢bCons → count d ≤ count Θ-dec
    Θ-max-count d d∈f = lookup (f[xs]≤f[argmax] {f = count} (witness Δ) a≢bCons) d∈f
```

**Maximality.**  If `d ∈ a≢bCons` contains `Θ`, then `d ⊆ Θ`: were the containment
proper on the enumerated carrier, `d` would out-count `Θ`, contradicting maximum
count.  The witness of properness is extracted from the *decidable* failure of
carrier-containment.

```agda
    Θ-max : ((d , pd) : DecCon 𝑨 ℓ) → (d , pd) ∈ a≢bCons → Θ ⊆ d → d ⊆ Θ
    Θ-max d d∈f Θ⊆d with all? (λ i → all? (λ j → ((i , j) ∈? d) →-dec ((i , j) ∈? Θ-dec)))
    ... | yes h = carrier-lift (proj₁ d) Θ h
    ... | no ¬h = ⊥-elim (n≮n (count d) (≤-<-trans (Θ-max-count d d∈f) cΘ<cd))
      where
      ¬hj = proj₂ (¬∀⟶∃¬ card _ (λ i → all? (λ j → (i , j) ∈? d  →-dec (i , j) ∈? Θ-dec )) ¬h)

      i₀ j₀ : Fin card
      i₀ = proj₁ (¬∀⟶∃¬ card _ (λ i → all? (λ j → (i , j) ∈? d →-dec (i , j) ∈? Θ-dec)) ¬h)
      j₀ = proj₁ (¬∀⟶∃¬ card _ (λ j → (i₀ , j) ∈? d →-dec (i₀ , j) ∈? Θ-dec) ¬hj)


      ¬impl = proj₂ (¬∀⟶∃¬ card _ (λ j → (i₀ , j) ∈? d →-dec (i₀ , j) ∈? Θ-dec) ¬hj)

      split = ¬→-split ((i₀ , j₀) ∈? d) ¬impl

      cΘ<cd : count Θ-dec < count d
      cΘ<cd = count-strict Θ-dec d i₀ j₀ Θ⊆d (proj₁ split) (proj₂ split)
```

#### Subdirect irreducibility of the maximal quotient

Let `Q = 𝑨 ╱ Θ`.  A congruence of `Q` *is* a congruence of `𝑨` containing `Θ`:
the underlying relation, equivalence proof, and compatibility carry over verbatim
(the quotient's operations are `𝑨`'s), and a `Q`-congruence's reflexivity over the
quotient equality `Θ` is exactly the containment `Θ ⊆ ·`.  `Q→A` records this.

```agda
    Q : Algebra α ℓ
    Q = 𝑨 ╱ Θ

    Q→A : Con Q ℓ → Con 𝑨 ℓ
    Q→A ψ = proj₁ ψ , mkcon r (is-equivalence (proj₂ ψ)) (is-compatible (proj₂ ψ))
      where r : ∀ {x y} → x ≈ y → proj₁ ψ x y
            r e = reflexive (proj₂ ψ) (reflexive (proj₂ Θ) e)
```

The monolith of `Q` is the principal congruence generated by the single pair
`(a , b)`.  It is nonzero (it relates `a , b`, which are `Q`-distinct), and it is
the least nonzero congruence: any nonzero `ψ` of `Q` corresponds to a congruence
`φ ⊇ Θ` of `𝑨`; choosing its representative `d ∈ cons`, if `d` did *not* relate
`a , b` then maximality would force `φ ⊆ Θ`, making `ψ` zero — so `d`, hence `φ`,
hence `ψ`, relates `a , b`, i.e. contains the principal congruence.

```agda
    Rₐᵦ : 𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type α
    Rₐᵦ x y = (x ≡ a) × (y ≡ b)

    μ : Con Q ℓ
    μ = Cg {𝑨 = Q} Rₐᵦ

    μ-nonzero : Nonzero Q μ
    μ-nonzero below = ¬Θab (below (base {𝑨 = Q} (refl , refl)))

    μ-least : (ψ : Con Q ℓ) → Nonzero Q ψ → μ ⊆ ψ
    μ-least ψ nz = Cg-least {𝑨 = Q} {R = Rₐᵦ} ψ R⊆ψ
      where
      φ : Con 𝑨 ℓ
      φ = Q→A ψ
      Θ⊆φ : Θ ⊆ φ
      Θ⊆φ = reflexive (proj₂ ψ)
      ψab : proj₁ ψ a b
      ψab with complete φ
      ... | d , d∈cons , φ⊆d , d⊆φ with proj₂ d a b
      ...   | yes dab = d⊆φ dab
      ...   | no ¬dab = ⊥-elim (nz (⊆-trans {θ = φ}{φ = proj₁ d}{ψ = Θ} φ⊆d
                          (Θ-max d (∈-filter⁺ notRel? d∈cons ¬dab)
                                   (⊆-trans {θ = Θ}{φ = φ}{ψ = proj₁ d} Θ⊆φ φ⊆d))))
      R⊆ψ : ∀ {x y} → Rₐᵦ x y → proj₁ ψ x y
      R⊆ψ (refl , refl) = ψab

    SI-Q : IsSubdirectlyIrreducible Q
    SI-Q = (a , b , ¬Θab)
         , (μ , record { mono-nonzero = μ-nonzero ; mono-least = μ-least })
```

#### Assembling the representation and the theorem

The index is the type of distinct pairs.  For each, `Θ` is the chosen maximal
congruence; the family **separates points** because, given any pair `x , y` not
already `≈`-equal (decidable!), `Θ` for `(x , y)` keeps them apart — so if every
member related them, they would be equal.  This is where decidable `≈` closes the
`¬¬`-gap the design note flags: the meet is *exactly* the diagonal.

```agda
  finiteSubdirectSIRep : SubdirectSIRep 𝑨 ℓ (α ⊔ ρ)
  finiteSubdirectSIRep = I , Θfam , separates , si
    where
    I : Type (α ⊔ ρ)
    I = Σ[ a ∈ 𝕌[ 𝑨 ] ] Σ[ b ∈ 𝕌[ 𝑨 ] ] ¬ (a ≈ b)

    Θfam : I → Con 𝑨 ℓ
    Θfam (a , b , a≢b) = Θ a b a≢b

    separates : Separates Θfam
    separates {x}{y} h with x ≟ y
    ... | yes x≈y = x≈y
    ... | no  x≢y = ⊥-elim (¬Θab x y x≢y (h (x , y , x≢y)))

    si : (i : I) → IsSubdirectlyIrreducible (𝑨 ╱ Θfam i)
    si (a , b , a≢b) = SI-Q a b a≢b
```

Birkhoff's subdirect representation theorem for finite algebras, unconditionally:
every finite algebra (with the decidable, complete congruence data above) is a
subdirect product of subdirectly irreducible algebras.

```agda
  finite-Birkhoff : SubdirectlyRepresentable 𝑨 ℓ (α ⊔ ρ)
  finite-Birkhoff = SIRep→Representable finiteSubdirectSIRep
```

#### Non-vacuity: the theorem fires

The finiteness interfaces are genuine, computational data — not disguised choice
principles — so they must be exhibited, not merely assumed.  The one-element
algebra `𝟏`{.AgdaFunction} satisfies both: its bare witness
`𝟏-FiniteAlgebra`{.AgdaFunction} is exhibited in [Setoid.Algebras.Finite][], and
its congruence-side witness `𝟏-FiniteCongruences`{.AgdaFunction} (a singleton
complete list) in [Setoid.Congruences.Finite][].  Feeding them to `finite-Birkhoff`
confirms the theorem fires (here on a degenerate input: the family of distinct
pairs is empty, so the trivial algebra is the subdirect product of the empty
family).  A genuinely subdirectly irreducible worked example — one that exercises
the maximal-congruence search — is the natural next addition.

```agda
-- The theorem applied: the one-element algebra is subdirectly representable.
𝟏-SubdirectlyRepresentable : SubdirectlyRepresentable 𝟏 (𝓞 ⊔ 𝓥) 0ℓ
𝟏-SubdirectlyRepresentable = finite-Birkhoff 𝟏-FiniteAlgebra 𝟏-FiniteCongruences
```

--------------------------------------

[^1]: This is option (b) of the design note `docs/notes/m6-2-subdirect.md`.
