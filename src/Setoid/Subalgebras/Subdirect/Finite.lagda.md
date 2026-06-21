---
layout: default
file: "src/Setoid/Subalgebras/Subdirect/Finite.lagda.md"
title: "Setoid.Subalgebras.Subdirect.Finite module (The Agda Universal Algebra Library)"
date: "2026-06-20"
author: "the agda-algebras development team"
---

### Finite Birkhoff: a constructive subdirect SI-representation

This is the [Setoid.Subalgebras.Subdirect.Finite][] module of the
[Agda Universal Algebra Library][].

[Setoid.Subalgebras.Subdirect][] proved the **choice-free core** of Birkhoff's
subdirect representation theorem and stated the full theorem `Birkhoff-subdirect`
*relative to* the choice principle `SubdirectSIRep 𝑨` — the existence, for every
algebra, of a separating family of congruences whose quotients are subdirectly
irreducible.  Producing that family for an arbitrary algebra is a Zorn's-lemma
step (a congruence maximal among those excluding a given pair), incompatible with
postulate-free `--safe`.

This module **discharges** that parameter for a class of *finite* algebras: it
constructs `SubdirectSIRep 𝑨` outright, with no choice and no postulate, and feeds
it to the choice-free reduction `SIRep→Representable`.  This is option (b) of the
design note `docs/notes/m6-2-subdirect.md`.

#### What "finite" must mean here, and why

The classical proof selects, for each pair `a ≢ b`, a congruence **maximal** among
those not relating `a` and `b`; such a congruence is completely meet-irreducible,
so its quotient is subdirectly irreducible.  To find that maximal congruence by a
*search* we must enumerate the congruence lattice, and to recognise subdirect
irreducibility (whose monolith condition quantifies over **all** congruences of the
quotient) the enumeration must be **complete** — every congruence equal, up to
mutual containment `≑`, to a listed one.

Crucially, *carrier-finiteness together with decidable setoid equality does not
suffice* to produce such an enumeration constructively.  A congruence is a
`Type`-valued relation `𝕌[ 𝑨 ] → 𝕌[ 𝑨 ] → Type ℓ`, and an arbitrary such relation
on a finite carrier need not be decidable: e.g. on a two-element carrier with no
operations, the relation that collapses the two points *iff* `P` holds is a
congruence for any proposition `P`, and it is `≑`-equal to a decidable congruence
only if `P` is decidable.  So a complete enumeration of congruences-up-to-`≑` is
strictly stronger than decidable `≈` on a finite carrier; it is exactly the
classical content of "finite algebra" for congruence-lattice purposes.

We therefore take that content as the finiteness interface: a `FiniteAlgebra`
bundles decidable `≈`, a finite enumeration of the carrier, and a finite list of
**decidable** congruences that is complete up to `≑`.  Everything downstream is
then fully constructive and computes.  Classically every finite algebra furnishes
this data, so `finite-Birkhoff` is Birkhoff's theorem for finite algebras; the
`FiniteAlgebra` record is precisely the constructive witness that makes the search
go through under `--safe`.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Subalgebras.Subdirect.Finite {𝑆 : Signature 𝓞 𝓥} where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                      using ( lsuc ) renaming ( Set to Type )
open import Data.Empty                          using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                       using ( Fin ; zero )
open import Data.Fin.Properties                 using ( all? ; ¬∀⟶∃¬ )
open import Data.List.Base                      using ( List ; [] ; _∷_ ; filter ; length ; allFin ; cartesianProduct )
open import Data.List.Extrema.Nat               using ( argmax ; f[xs]≤f[argmax] ; argmax-sel )
open import Data.List.Membership.Propositional  using ( _∈_ )
open import Data.List.Membership.Propositional.Properties using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-cartesianProduct⁺ ; ∈-allFin )
open import Data.List.Relation.Unary.All        using ( lookup )
open import Data.List.Relation.Unary.Any        using ( here ; there )
open import Data.Nat.Base                       using ( ℕ ; _≤_ ; _<_ ; z≤n ; s≤s )
open import Data.Nat.Properties                 using ( m≤n⇒m≤1+n ; n<1+n ; <-trans ; ≤-<-trans ; n≮n )
open import Data.Product                        using ( _×_ ; _,_ ; Σ-syntax ; ∃-syntax ; proj₁ ; proj₂ )
open import Data.Sum.Base                       using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit.Base                      using ( ⊤ ; tt )
open import Function                            using ( Func )
open import Level                               using ( Level ; _⊔_ ; 0ℓ ; Lift ; lift ; lower )
open import Relation.Binary                     using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality as ≡ using ( _≡_ )
open import Relation.Nullary                    using ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable          using ( _→-dec_ ; ¬? )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Basic      {𝑆 = 𝑆}  using  ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Congruences.Basic   {𝑆 = 𝑆}  using  ( Con ; mkcon ; _∣≈_ ; reflexive
                                                       ; is-equivalence ; is-compatible ; _╱_ ; 𝟘[_] )
open import Setoid.Congruences.Lattice {𝑆 = 𝑆}  using  ( _⊆_ ; _≑_ ; ⊆-trans )
open import Setoid.Congruences.Generation {𝑆 = 𝑆} using  ( Cg ; Cg-least ; base )
open import Setoid.Congruences.Monolith {𝑆 = 𝑆} using  ( IsSubdirectlyIrreducible ; IsMonolith
                                                          ; mono-nonzero ; mono-least ; Nonzero )

open import Setoid.Subalgebras.Subdirect.Basic {𝑆 = 𝑆} using ( Separates )
open import Setoid.Subalgebras.Subdirect.BirkhoffSI {𝑆 = 𝑆}
  using (SubdirectSIRep; SubdirectlyRepresentable ; SIRep→Representable )

open Algebra using ( Domain ; Interp )
open Func    using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```

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
    filter-length-strict (x ∷ xs) (here ≡.refl) qw ¬pw with P? x | Q? x
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

#### Decidable congruences and the finiteness interface

A **decidable congruence** is a congruence whose membership relation is decidable.
The working congruence level is the absorbing level `clv α ρ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ`, at
which the generated (principal) congruences used for the monolith stay put — the
same level discipline as [Setoid.Congruences.CompleteLattice][].

```agda
-- The absorbing congruence level at which everything below is carried out.
clv : (α ρ : Level) → Level
clv α ρ = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ

-- A congruence together with a decision procedure for its membership.
DecCon : (𝑨 : Algebra α ρ)(ℓ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ lsuc ℓ)
DecCon 𝑨 ℓ = Σ[ θ ∈ Con 𝑨 ℓ ] (∀ x y → Dec (proj₁ θ x y))
```

The finiteness interface bundles: decidable `≈`; a surjective enumeration of the
carrier (used to *count* related pairs); and a finite, complete list of decidable
congruences (the searchable congruence lattice).  See the module header for why
the last field cannot be derived from the first two.

```agda
record FiniteAlgebra (𝑨 : Algebra α ρ) : Type (lsuc (clv α ρ)) where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
  field
    _≟_       : (x y : 𝕌[ 𝑨 ]) → Dec (x ≈ y)
    card      : ℕ
    enum      : Fin card → 𝕌[ 𝑨 ]
    enum-sur  : (x : 𝕌[ 𝑨 ]) → Σ[ i ∈ Fin card ] (enum i ≈ x)
    cons      : List (DecCon 𝑨 (clv α ρ))
    complete  : (φ : Con 𝑨 (clv α ρ))
              → Σ[ d ∈ DecCon 𝑨 (clv α ρ) ] (d ∈ cons) × (φ ≑ proj₁ d)
```

#### The construction

Fix a finite algebra.  We abbreviate the working level as `ℓ`, and `pairs` is the
list of all index pairs of the carrier enumeration.

```agda
module _ {𝑨 : Algebra α ρ} (𝑭 : FiniteAlgebra 𝑨) where
  open FiniteAlgebra 𝑭
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym )

  ℓ : Level
  ℓ = clv α ρ

  pairs : List (Fin card × Fin card)
  pairs = cartesianProduct (allFin card) (allFin card)

  -- The decision procedure that a decidable congruence relates the i-th and j-th
  -- enumerated carrier elements, and the count of all such related index pairs.
  pred : (d : DecCon 𝑨 ℓ)(p : Fin card × Fin card)
       → Dec (proj₁ (proj₁ d) (enum (proj₁ p)) (enum (proj₂ p)))
  pred d (i , j) = proj₂ d (enum i) (enum j)

  count : DecCon 𝑨 ℓ → ℕ
  count d = length (filter (pred d) pairs)
```

A congruence contained in another relates no more pairs (`count-mono`); if the
containment is *proper on the enumerated carrier* it relates strictly fewer
(`count-strict`).  Both are instances of the generic list lemmas.

```agda
  count-mono : (d e : DecCon 𝑨 ℓ) → proj₁ d ⊆ proj₁ e → count d ≤ count e
  count-mono d e d⊆e = filter-length-mono (pred d) (pred e) (λ {p} → d⊆e) pairs

  count-strict : (d e : DecCon 𝑨 ℓ)(i j : Fin card)
               → proj₁ d ⊆ proj₁ e
               → proj₁ (proj₁ e) (enum i) (enum j)
               → ¬ proj₁ (proj₁ d) (enum i) (enum j)
               → count d < count e
  count-strict d e i j d⊆e eij ¬dij =
    filter-length-strict (pred d) (pred e) (λ {p} → d⊆e)
                         pairs (∈-cartesianProduct⁺ (∈-allFin i) (∈-allFin j)) eij ¬dij
```

A relation that holds on every enumerated pair holds everywhere, because the
enumeration is surjective and congruences respect `≈`.  This lifts a
carrier-level containment to a genuine containment of congruences.

```agda
  carrier-lift : (R S : Con 𝑨 ℓ)
               → (∀ i j → proj₁ R (enum i) (enum j) → proj₁ S (enum i) (enum j))
               → R ⊆ S
  carrier-lift R S h {x}{y} Rxy = Strans (Srefl (sym eᵢ≈x)) (Strans Sᵢⱼ (Srefl eⱼ≈y))
    where
    Rrefl   = reflexive (proj₂ R)
    Rtrans  = IsEquivalence.trans (is-equivalence (proj₂ R))
    Srefl   = reflexive (proj₂ S)
    Strans  = IsEquivalence.trans (is-equivalence (proj₂ S))
    i = proj₁ (enum-sur x) ; eᵢ≈x = proj₂ (enum-sur x)
    j = proj₁ (enum-sur y) ; eⱼ≈y = proj₂ (enum-sur y)
    Rᵢⱼ : proj₁ R (enum i) (enum j)
    Rᵢⱼ = Rtrans (Rrefl eᵢ≈x) (Rtrans Rxy (Rrefl (sym eⱼ≈y)))
    Sᵢⱼ : proj₁ S (enum i) (enum j)
    Sᵢⱼ = h i j Rᵢⱼ
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
    notrel? : (d : DecCon 𝑨 ℓ) → Dec (¬ proj₁ (proj₁ d) a b)
    notrel? d = ¬? (proj₂ d a b)

    filtered : List (DecCon 𝑨 ℓ)
    filtered = filter notrel? cons

    -- The diagonal's representative does not relate a and b (it relates only
    -- ≈-equal pairs), so it lies in `filtered`.
    dΔ : DecCon 𝑨 ℓ
    dΔ = proj₁ (complete Δ)
    ¬dΔab : ¬ proj₁ (proj₁ dΔ) a b
    ¬dΔab dab = a≢b (lower (proj₂ (proj₂ (proj₂ (complete Δ))) dab))
    dΔ∈filtered : dΔ ∈ filtered
    dΔ∈filtered = ∈-filter⁺ notrel? (proj₁ (proj₂ (complete Δ))) ¬dΔab

    -- The chosen congruence: a maximum-count member of `filtered`.
    Θ-dec : DecCon 𝑨 ℓ
    Θ-dec = argmax count dΔ filtered

    Θ-dec∈filtered : Θ-dec ∈ filtered
    Θ-dec∈filtered with argmax-sel count dΔ filtered
    ... | inj₁ eq = ≡.subst (_∈ filtered) (≡.sym eq) dΔ∈filtered
    ... | inj₂ ∈f = ∈f

    Θ : Con 𝑨 ℓ
    Θ = proj₁ Θ-dec

    ¬Θab : ¬ proj₁ Θ a b
    ¬Θab = proj₂ (∈-filter⁻ notrel? {xs = cons} Θ-dec∈filtered)

    -- count d ≤ count Θ for every member of `filtered`: Θ has maximum count.
    Θ-max-count : (d : DecCon 𝑨 ℓ) → d ∈ filtered → count d ≤ count Θ-dec
    Θ-max-count d d∈f = lookup (f[xs]≤f[argmax] {f = count} dΔ filtered) d∈f
```

**Maximality.**  If `d ∈ filtered` contains `Θ`, then `d ⊆ Θ`: were the containment
proper on the enumerated carrier, `d` would out-count `Θ`, contradicting maximum
count.  The witness of properness is extracted from the *decidable* failure of
carrier-containment.

```agda
    Θ-max : (d : DecCon 𝑨 ℓ) → d ∈ filtered → Θ ⊆ proj₁ d → proj₁ d ⊆ Θ
    Θ-max d d∈f Θ⊆d with all? (λ i → all? (λ j → pred d (i , j) →-dec pred Θ-dec (i , j)))
    ... | yes h = carrier-lift (proj₁ d) Θ h
    ... | no ¬h = ⊥-elim (n≮n (count d) (≤-<-trans (Θ-max-count d d∈f) cΘ<cd))
      where
      i₀ = proj₁ (¬∀⟶∃¬ card _ (λ i → all? (λ j → pred d (i , j) →-dec pred Θ-dec (i , j))) ¬h)
      ¬hj = proj₂ (¬∀⟶∃¬ card _ (λ i → all? (λ j → pred d (i , j) →-dec pred Θ-dec (i , j))) ¬h)
      j₀ = proj₁ (¬∀⟶∃¬ card _ (λ j → pred d (i₀ , j) →-dec pred Θ-dec (i₀ , j)) ¬hj)
      ¬impl = proj₂ (¬∀⟶∃¬ card _ (λ j → pred d (i₀ , j) →-dec pred Θ-dec (i₀ , j)) ¬hj)
      split = ¬→-split (pred d (i₀ , j₀)) ¬impl
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
    μ-nonzero below = ¬Θab (below (base {𝑨 = Q} (≡.refl , ≡.refl)))

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
                          (Θ-max d (∈-filter⁺ notrel? d∈cons ¬dab)
                                   (⊆-trans {θ = Θ}{φ = φ}{ψ = proj₁ d} Θ⊆φ φ⊆d))))
      R⊆ψ : ∀ {x y} → Rₐᵦ x y → proj₁ ψ x y
      R⊆ψ (≡.refl , ≡.refl) = ψab

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

#### Non-vacuity: the interface is inhabited

The `FiniteAlgebra` record is genuine, computational data — not a disguised choice
principle — so it must be exhibited, not merely assumed.  The one-element algebra
over any signature satisfies it: its carrier is `⊤`, decidable equality is trivial,
and its only congruence (up to `≑`) is the diagonal, so the complete list is a
singleton.  This confirms `finite-Birkhoff` fires (here on a degenerate input: the
family of distinct pairs is empty, so the trivial algebra is the subdirect product
of the empty family).  A genuinely subdirectly irreducible worked example — one
that exercises the maximal-congruence search — is the natural next addition.

```agda
-- The one-element algebra over the signature 𝑆.
𝟏 : Algebra 0ℓ 0ℓ
Domain 𝟏 = record  { Carrier        = ⊤
                   ; _≈_            = λ _ _ → ⊤
                   ; isEquivalence  = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }
Interp 𝟏 ⟨$⟩ _    = tt
cong (Interp 𝟏) _ = tt

-- Its sole decidable congruence: the all-relation (= the diagonal on a point).
𝟏-Δ : DecCon 𝟏 (clv 0ℓ 0ℓ)
𝟏-Δ = ((λ _ _ → Lift (clv 0ℓ 0ℓ) ⊤)
      , mkcon  (λ _ → lift tt)
               (record { refl = lift tt ; sym = λ _ → lift tt ; trans = λ _ _ → lift tt })
               (λ _ _ → lift tt))
      , (λ _ _ → yes (lift tt))

𝟏-FiniteAlgebra : FiniteAlgebra 𝟏
𝟏-FiniteAlgebra = record
  { _≟_       = λ _ _ → yes tt
  ; card      = 1
  ; enum      = λ _ → tt
  ; enum-sur  = λ _ → zero , tt
  ; cons      = 𝟏-Δ ∷ []
  ; complete  = λ φ → 𝟏-Δ , here ≡.refl , (λ _ → lift tt) , (λ _ → reflexive (proj₂ φ) tt)
  }

-- The theorem applied: the one-element algebra is subdirectly representable.
𝟏-SubdirectlyRepresentable : SubdirectlyRepresentable 𝟏 (clv 0ℓ 0ℓ) 0ℓ
𝟏-SubdirectlyRepresentable = finite-Birkhoff 𝟏-FiniteAlgebra
```

--------------------------------------

<span style="float:left;">[← Setoid.Subalgebras.Subdirect](Setoid.Subalgebras.Subdirect.html)</span>
<span style="float:right;">[Setoid.Subalgebras.Properties →](Setoid.Subalgebras.Properties.html)</span>

{% include UALib.Links.md %}
