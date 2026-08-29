---
layout: default
file: "src/FLRP/Closure/FilterIdeal.lagda.md"
title: "FLRP.Closure.FilterIdeal module (The Agda Universal Algebra Library)"
date: "2026-08-17"
author: "the agda-algebras development team"
---

### Snow's filter-ideal lemma at Layer D

This is the [FLRP.Closure.FilterIdeal][] module of the [Agda Universal Algebra Library][].

**The lemma** (Snow, *Algebra Universalis* 43 (2000); reproved directly in
`docs/papers/fin-lat-rep/SmallLatticeReps.tex` § "Union of a filter and ideal",
`lemma:union-filter-ideal`): if `L ≤ Eq(X)` is representable over a finite set
`X` and `L₀ ≤ L` is a sublattice with universe `α↑ ∪ β↓` for some
`α, β ∈ L`, then `L₀` is representable.  The manuscript's proof is four lines
and entirely constructive: writing `λ(L)` for the monoid of unary maps
respecting every member of `L` (the *preserving monoid* of
`scripts/python/flrp/eqsearch.py`, whose *closure test* `Inv(M) = L` is the
representability notion in play), it takes `θ ∈ L ∖ L₀`, picks witnesses
`(a , b) ∈ α ∖ θ` and `(u , v) ∈ θ ∖ β`, and defines the two-valued map

```text
h(x) = a  if x ∈ u/β,        h(x) = b  otherwise.
```

Then `β ≤ ker h`, so `h` respects everything below `β`; and `(a , b) ∈ γ` for
every `γ ≥ α`, so `h` respects everything above `α`.  Hence `h ∈ λ(L₀)` while
`h` violates `θ` at the pair `(u , v)`.  Since `λ(L) ⊆ λ(L₀)`, every
`θ ∉ L₀` is violated by some member of `λ(L₀)`, i.e. `L₀ = Con ⟨X , λ(L₀)⟩`.

**The formalization** works at Layer D of the two-layer congruence discipline
(ADR-008), with decidable congruences in place of subsets of `Eq(X)`.  Rather
than manipulating the full function monoid `λ(L₀)` — which is never needed and
could not be enumerated — the ambient lattice is presented as the congruence
lattice of an algebra `𝑨`, and the representing algebra of `L₀` is the
**extension** `𝑩` of `𝑨` by one unary operation `h(a , b , u)` per triple of
carrier elements: the manuscript's two-valued map when `(a , b)` is an
`α`-pair, and the identity otherwise (so that the symbol family is total).
Both halves of the manuscript proof survive verbatim:

+  each `h(a , b , u)` respects every congruence in the filter-ideal union
   (`hMap-compat`{.AgdaFunction}, the formal reading of `h ∈ λ(L₀)`), so every
   member of the union remains a congruence of `𝑩` (`liftᵈ`{.AgdaFunction});
+  a decidable congruence of `𝑩` outside both the filter and the ideal is
   impossible (`h-violation`{.AgdaFunction}): the witness extraction
   `⊈ᵈ-witness`{.AgdaFunction} of [FLRP.Representable][] supplies the pairs
   `(a , b)` and `(u , v)` constructively, and compatibility with the
   congruence's *own* `h` operation at `(u , v)` is the contradiction.

The classification `snow`{.AgdaFunction} — every decidable congruence of `𝑩`
lies in `α↑ ∪ β↓` — follows by deciding the two containments
(`⊆ᵈ-dec`{.AgdaFunction}).  The `Assembly`{.AgdaModule} submodule then turns a
*closed finite family* presenting the union (in the sense of the engine's
closure test: every congruence of `𝑨` in the union is `≑` a listed member)
into the order isomorphism `ConIsoᵈ 𝑩 𝑳₀`{.AgdaFunction} and the
`Representableᵈ`{.AgdaRecord} witness — with **no postulate and no registry
assumption**, in contrast to the Kurzweil–Netter duality route
(`dual-Representableᵈ`{.AgdaFunction} of [FLRP.Closure.Basic][]).

The order-theoretic half of the lemma — `α↑ ∪ β↓` is always a sublattice — is
[Classical.Structures.Lattice.FilterIdeal][]; nothing here depends on it, but
the case analyses are the same four lines.  The manuscript also derives
*adjoined ordinal sums* as a corollary of this lemma (`α = β = 1_{L₁} × 0_{L₂}`
inside `L₁ × L₂`); the library proves ordinal-sum closure directly in
[FLRP.Closure.OrdinalSum][], so the corollary is a free consistency check
between the two routes rather than new mathematics.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.Closure.FilterIdeal where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty          using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base       using ( Fin ; _↑ˡ_ ; _↑ʳ_ ; splitAt ; combine
                                      ; remQuot )
open import Data.Fin.Patterns   using ( 0F )
open import Data.Fin.Properties using ( splitAt-↑ˡ ; splitAt-↑ʳ ; remQuot-combine )
open import Data.Nat.Base       using ( ℕ ; _+_ ; _*_ )
open import Data.Product        using ( _×_ ; _,_ ; Σ-syntax ; ∃-syntax
                                      ; proj₁ ; proj₂ )
open import Data.Sum.Base       using ( _⊎_ ; inj₁ ; inj₂ ; [_,_] )
                                renaming ( map to ⊎-map )
open import Function.Construct.Identity            using ( ↔-id )
open import Level                                  using ( 0ℓ ; lift ; lower )
open import Relation.Binary                        using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; trans ; cong
                                                         ; cong₂ ; subst₂ )
open import Relation.Nullary                       using ( ¬_ ; Dec ; yes ; no )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice     using  ( module Lattice-Order )
open import FLRP.Problem                     using  ( FiniteLattice ; toLattice )
open import FLRP.Representable               using  ( _⊆ᵈ_ ; _≑ᵈ_ ; ConIsoᵈ
                                                    ; Representableᵈ ; ⊆ᵈ-dec
                                                    ; ⊈ᵈ-witness ; ConRel-resp )
open import Overture                         using  ( Signature ; OperationSymbolsOf
                                                    ; ArityOf )
open import Overture.Operations              using  ( Op )
open import Setoid.Algebras.Basic            using  ( Algebra ; 𝔻[_] ; 𝕌[_]
                                                    ; mkAlgebra ; _^_ )
open import Setoid.Algebras.Finite           using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic         using  ( Con ; mkcon ; _∣≈_ ; reflexive
                                                    ; is-equivalence ; is-compatible
                                                    ; 𝟘[_] )
open import Setoid.Congruences.Finite.Basic  using  ( DecCon ; ConRel )
open import Setoid.Congruences.Lattice       using  ( _≑_ )
open import Setoid.Signatures.Finite         using  ( FiniteSignature )
```
-->

#### The setting

The construction is parameterized by the ambient algebra `𝑨`{.AgdaBound} (over
an arbitrary finite-level signature), its carrier-finiteness witness, and the
two distinguished decidable congruences `α`{.AgdaBound} and `β`{.AgdaBound}.
Nothing requires `α`{.AgdaBound} and `β`{.AgdaBound} to be comparable, or the
ambient signature to be unary — the intended instances (coset algebras of
finite groups) are unary, but the extension construction is uniform.

```agda
module FilterIdealClosure  {𝑆 : Signature 0ℓ 0ℓ} (𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ)
                           (𝑭 : FiniteAlgebra 𝑨) (α β : DecCon 𝑨 0ℓ)
  where

  private
    X : Type 0ℓ
    X = 𝕌[ 𝑨 ]

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( sym to ≈sym )
  open FiniteAlgebra
```

#### The extended signature

One extra unary symbol per triple `(a , b , u)` of carrier elements — the
parameters of the manuscript's map `h`: the intended `α`-pair `(a , b)` and the
`β`-class representative `u`.

```agda
  -- The symbol type of the h operations: one per carrier triple.
  HSym : Type 0ℓ
  HSym = X × X × X

  -- The extended signature: the symbols of 𝑆, plus the h symbols (all unary).
  𝑆⁺ : Signature 0ℓ 0ℓ
  𝑆⁺ = (OperationSymbolsOf 𝑆 ⊎ HSym) , [ ArityOf 𝑆 , (λ _ → Fin 1) ]
```

#### The h maps

Following the house pattern of [FLRP.Representable][]'s
`decToFin`{.AgdaFunction}, the value of `h` is a pure function
`hVal`{.AgdaFunction} of the two decision *verdicts* — is `(a , b)` an
`α`-pair, and is `x` in the `β`-class of `u`? — so that the case analyses
below can re-expose the decisions as explicit arguments.  When `(a , b)` is
not an `α`-pair the map is the identity, which respects everything; this is
what makes the symbol family total without a Σ-constraint on the triples.

```agda
  private
    -- The manuscript's two-valued map, as a function of the two verdicts:
    -- constant a on the β-class of u, constant b off it, identity if (a , b)
    -- is not an α-pair.
    hVal : {P Q : Type 0ℓ} → X → X → X → Dec P → Dec Q → X
    hVal a b x (no  _)  _        = x
    hVal a b x (yes _)  (yes _)  = a
    hVal a b x (yes _)  (no  _)  = b

    -- A positive α-verdict and a positive β-verdict land on a ...
    hVal-const-a :  {P Q : Type 0ℓ} (a b x : X) (dp : Dec P) (dq : Dec Q)
      →             P → Q → hVal a b x dp dq ≡ a
    hVal-const-a a b x (yes _)  (yes _)  _ _  = _≡_.refl
    hVal-const-a a b x (yes _)  (no ¬q)  _ q  = ⊥-elim (¬q q)
    hVal-const-a a b x (no ¬p)  _        p _  = ⊥-elim (¬p p)

    -- ... a positive α-verdict and a negative β-verdict land on b.
    hVal-const-b :  {P Q : Type 0ℓ} (a b x : X) (dp : Dec P) (dq : Dec Q)
      →             P → ¬ Q → hVal a b x dp dq ≡ b
    hVal-const-b a b x (yes _)  (no _)   _ _   = _≡_.refl
    hVal-const-b a b x (yes _)  (yes q)  _ ¬q  = ⊥-elim (¬q q)
    hVal-const-b a b x (no ¬p)  _        p _   = ⊥-elim (¬p p)

  -- The h operation of the triple (a , b , u), evaluated by running the
  -- decision procedures of α and β.
  hMap : HSym → X → X
  hMap (a , b , u) x = hVal a b x (proj₂ α a b) (proj₂ β u x)
```

The map respects the carrier's setoid equality: the `α`-verdict is fixed, and
`≈`-equal arguments receive the same `β`-verdict because congruences respect
`≈` (`ConRel-resp`{.AgdaFunction}).

```agda
  hMap-cong : (s : HSym) {x y : X} → x ≈ y → hMap s x ≈ hMap s y
  hMap-cong (a , b , u) {x} {y} x≈y = aux (proj₂ α a b) (proj₂ β u x) (proj₂ β u y)
    where
    open Setoid 𝔻[ 𝑨 ] using () renaming ( refl to ≈refl )

    aux :  {P : Type 0ℓ} (dp : Dec P)
           (dx : Dec (ConRel β u x)) (dy : Dec (ConRel β u y))
      →    hVal a b x dp dx ≈ hVal a b y dp dy
    aux (no _)   _          _          = x≈y
    aux (yes _)  (yes _)    (yes _)    = ≈refl
    aux (yes _)  (no _)     (no _)     = ≈refl
    aux (yes _)  (yes βux)  (no ¬βuy)  = ⊥-elim (¬βuy (ConRel-resp β ≈refl x≈y βux))
    aux (yes _)  (no ¬βux)  (yes βuy)  = ⊥-elim (¬βux (ConRel-resp β ≈refl (≈sym x≈y) βuy))
```

#### The extended algebra

`𝑩`{.AgdaFunction} interprets the old symbols exactly as `𝑨`{.AgdaBound} does
and each new symbol by its `hMap`{.AgdaFunction}, on the *same* carrier
setoid.  The congruence obligation for the old symbols is discharged through
the diagonal congruence of `𝑨`{.AgdaBound} (whose compatibility field *is* the
statement that the operations respect `≈`).

```agda
  private
    -- The operations of 𝑨 respect ≈, read off the diagonal congruence.
    ≈-compat :  (f : OperationSymbolsOf 𝑆) {u v : ArityOf 𝑆 f → X}
      →         (∀ i → u i ≈ v i) → (f ^ 𝑨) u ≈ (f ^ 𝑨) v
    ≈-compat f h = lower (is-compatible (proj₂ (𝟘[ 𝑨 ] {0ℓ})) f (λ i → lift (h i)))

    -- The interpretation of the extended signature.
    interp⁺ : (o : OperationSymbolsOf 𝑆⁺) → Op (ArityOf 𝑆⁺ o) X
    interp⁺ (inj₁ f)  = f ^ 𝑨
    interp⁺ (inj₂ s)  = λ as → hMap s (as 0F)

    interp⁺-cong :  (o : OperationSymbolsOf 𝑆⁺) {u v : ArityOf 𝑆⁺ o → X}
      →            (∀ i → u i ≈ v i) → interp⁺ o u ≈ interp⁺ o v
    interp⁺-cong (inj₁ f)  h = ≈-compat f h
    interp⁺-cong (inj₂ s)  h = hMap-cong s (h 0F)

  -- The extension of 𝑨 by the h operations, on the same carrier setoid.
  𝑩 : Algebra {𝑆 = 𝑆⁺} 0ℓ 0ℓ
  𝑩 = mkAlgebra 𝔻[ 𝑨 ] interp⁺ interp⁺-cong

  -- Carrier finiteness is inherited: the domain setoid is unchanged.
  𝑩-FiniteAlgebra : FiniteAlgebra 𝑩
  𝑩-FiniteAlgebra ._≟_       = 𝑭 ._≟_
  𝑩-FiniteAlgebra .card      = 𝑭 .card
  𝑩-FiniteAlgebra .enum      = 𝑭 .enum
  𝑩-FiniteAlgebra .enum-sur  = 𝑭 .enum-sur
```

#### Restriction, the filter-ideal union, and lifting

A decidable congruence of `𝑩`{.AgdaFunction} restricts to one of
`𝑨`{.AgdaBound} by forgetting compatibility with the h symbols; the underlying
relation is unchanged.

```agda
  -- Restriction along the signature inclusion: same relation, fewer operations.
  restrictᵈ : DecCon 𝑩 0ℓ → DecCon 𝑨 0ℓ
  restrictᵈ ((θ , θcon) , θ?) =
    ( θ , mkcon  (reflexive θcon) (is-equivalence θcon)
                 (λ f → is-compatible θcon (inj₁ f)) )
    , θ?
```

`InFilterIdeal γ`{.AgdaFunction} is membership of a congruence in the universe
`α↑ ∪ β↓` of the sublattice `L₀`, stated by containment.

```agda
  -- γ lies in the filter above α or in the ideal below β.
  InFilterIdeal : DecCon 𝑨 0ℓ → Type 0ℓ
  InFilterIdeal γ = (α ⊆ᵈ γ) ⊎ (γ ⊆ᵈ β)
```

The first half of the manuscript proof: every `h` operation respects every
congruence in the union.  In the filter case the values of `h` lie in
`{a , b}` and `(a , b)` is an `α`-pair, hence a `γ`-pair; in the ideal case
`γ ⊆ β ⊆ ker h`, so `γ`-related arguments receive the same value.  (Together
with the trivial observation that the operations of `𝑨`{.AgdaBound} respect
every congruence of `𝑨`{.AgdaBound}, this is precisely the manuscript's
`ops(𝑩) ⊆ λ(L₀)`.)

```agda
  hMap-compat :  (s : HSym) (γ : DecCon 𝑨 0ℓ) → InFilterIdeal γ
    →            {x y : X} → ConRel γ x y → ConRel γ (hMap s x) (hMap s y)
  hMap-compat (a , b , u) γ (inj₁ α⊆γ) {x} {y} γxy =
    aux (proj₂ α a b) (proj₂ β u x) (proj₂ β u y)
    where
    γ-refl : ∀ {z} → ConRel γ z z
    γ-refl = IsEquivalence.refl (is-equivalence (proj₂ (proj₁ γ)))

    γ-sym : ∀ {z w} → ConRel γ z w → ConRel γ w z
    γ-sym = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ γ)))

    -- In the filter case the h values are α-related, hence γ-related.
    aux :  (dp : Dec (ConRel α a b))
           (dx : Dec (ConRel β u x)) (dy : Dec (ConRel β u y))
      →    ConRel γ (hVal a b x dp dx) (hVal a b y dp dy)
    aux (no _)      _        _        = γxy
    aux (yes _)     (yes _)  (yes _)  = γ-refl
    aux (yes _)     (no _)   (no _)   = γ-refl
    aux (yes αab)   (yes _)  (no _)   = α⊆γ αab
    aux (yes αab)   (no _)   (yes _)  = γ-sym (α⊆γ αab)
  hMap-compat (a , b , u) γ (inj₂ γ⊆β) {x} {y} γxy =
    aux (proj₂ α a b) (proj₂ β u x) (proj₂ β u y)
    where
    γ-refl : ∀ {z} → ConRel γ z z
    γ-refl = IsEquivalence.refl (is-equivalence (proj₂ (proj₁ γ)))

    β-sym : ∀ {z w} → ConRel β z w → ConRel β w z
    β-sym = IsEquivalence.sym (is-equivalence (proj₂ (proj₁ β)))

    β-trans : ∀ {z w t} → ConRel β z w → ConRel β w t → ConRel β z t
    β-trans = IsEquivalence.trans (is-equivalence (proj₂ (proj₁ β)))

    -- In the ideal case γ ⊆ β ⊆ ker h: γ-related arguments share a β-class
    -- verdict, so h sends them to literally the same value.
    aux :  (dp : Dec (ConRel α a b))
           (dx : Dec (ConRel β u x)) (dy : Dec (ConRel β u y))
      →    ConRel γ (hVal a b x dp dx) (hVal a b y dp dy)
    aux (no _)   _          _          = γxy
    aux (yes _)  (yes _)    (yes _)    = γ-refl
    aux (yes _)  (no _)     (no _)     = γ-refl
    aux (yes _)  (yes βux)  (no ¬βuy)  = ⊥-elim (¬βuy (β-trans βux (γ⊆β γxy)))
    aux (yes _)  (no ¬βux)  (yes βuy)  = ⊥-elim (¬βux (β-trans βuy (β-sym (γ⊆β γxy))))
```

Consequently every congruence of `𝑨`{.AgdaBound} in the union lifts to a
congruence of `𝑩`{.AgdaFunction} with the same underlying relation.

```agda
  -- A member of the filter-ideal union is a congruence of the extension.
  liftᵈ : (γ : DecCon 𝑨 0ℓ) → InFilterIdeal γ → DecCon 𝑩 0ℓ
  liftᵈ γ@((θ , θcon) , θ?) mem =
    ( θ , mkcon (reflexive θcon) (is-equivalence θcon) compat ) , θ?
    where
    compat : 𝑩 ∣≈ θ
    compat (inj₁ f)  = is-compatible θcon f
    compat (inj₂ s)  = λ h → hMap-compat s γ mem (h 0F)
```

#### The violation step and the classification

The second half of the manuscript proof.  Suppose a decidable congruence of
`𝑩`{.AgdaFunction} lies outside the filter *and* outside the ideal.  Both
failed containments yield concrete witnesses (`⊈ᵈ-witness`{.AgdaFunction}):
an `α`-pair `(a , b)` not related by the congruence, and a related pair
`(u , v)` that is not a `β`-pair.  The congruence must be compatible with its
own operation `h(a , b , u)` — but that operation sends `(u , v)` to
`(a , b)`, a contradiction.

```agda
  h-violation :  (d : DecCon 𝑩 0ℓ)
    →            ¬ (α ⊆ᵈ restrictᵈ d) → ¬ (restrictᵈ d ⊆ᵈ β) → ⊥
  h-violation d ¬filter ¬ideal = step
    where
    θ : Con 𝑩 0ℓ
    θ = proj₁ d

    wα = ⊈ᵈ-witness 𝑭 α (restrictᵈ d) ¬filter
    wβ = ⊈ᵈ-witness 𝑭 (restrictᵈ d) β ¬ideal

    a b u v : X
    a = proj₁ wα
    b = proj₁ (proj₂ wα)
    u = proj₁ wβ
    v = proj₁ (proj₂ wβ)

    αab : ConRel α a b
    αab = proj₁ (proj₂ (proj₂ wα))

    ¬θab : ¬ ConRel d a b
    ¬θab = proj₂ (proj₂ (proj₂ wα))

    θuv : ConRel d u v
    θuv = proj₁ (proj₂ (proj₂ wβ))

    ¬βuv : ¬ ConRel β u v
    ¬βuv = proj₂ (proj₂ (proj₂ wβ))

    β-refl : ConRel β u u
    β-refl = IsEquivalence.refl (is-equivalence (proj₂ (proj₁ β)))

    -- Compatibility of the congruence with its own h operation, at (u , v).
    θ-h : ConRel d (hMap (a , b , u) u) (hMap (a , b , u) v)
    θ-h = is-compatible (proj₂ θ) (inj₂ (a , b , u)) {λ _ → u} {λ _ → v} (λ _ → θuv)

    -- h sends u to a (u is in its own β-class) and v to b ((u , v) ∉ β).
    step : ⊥
    step = ¬θab (subst₂ (ConRel d)
             (hVal-const-a a b u (proj₂ α a b) (proj₂ β u u) αab β-refl)
             (hVal-const-b a b v (proj₂ α a b) (proj₂ β u v) αab ¬βuv)
             θ-h)
```

Snow's lemma, classification form: deciding the two containments over the
finite carrier leaves the impossible case to the violation step.

```agda
  -- Every decidable congruence of the extension lies in the filter or the ideal.
  snow : (d : DecCon 𝑩 0ℓ) → InFilterIdeal (restrictᵈ d)
  snow d with ⊆ᵈ-dec 𝑭 α (restrictᵈ d)
  ... | yes filter  = inj₁ filter
  ... | no ¬filter with ⊆ᵈ-dec 𝑭 (restrictᵈ d) β
  ...   | yes ideal  = inj₂ ideal
  ...   | no ¬ideal  = ⊥-elim (h-violation d ¬filter ¬ideal)
```

#### Assembly: from a closed finite family to `Representableᵈ`

The remaining inputs are exactly the Layer-D presentation data of the
sublattice `L₀`:

+  the abstract target `𝑳`{.AgdaBound}, a `FiniteLattice`{.AgdaRecord} whose
   carrier indexes the members of `L₀`;
+  the concrete family `γ`{.AgdaBound} of decidable congruences of
   `𝑨`{.AgdaBound}, each in the union (`γ-mem`{.AgdaBound});
+  **closedness** of the family (`classify`{.AgdaBound}): every congruence of
   `𝑨`{.AgdaBound} in the union is `≑` a listed member — the constructive
   content of the engine-side closure test `Inv(λ(L₀)) = L₀`, supplied per
   application (for the coset-algebra instances it is the WP-3 bridge
   composed with a subgroup-interval classification);
+  order agreement (`γ-mono`{.AgdaBound} / `γ-reflect`{.AgdaBound}):
   containment of family members matches the meet order of the target's
   tables.

Nothing here forces any of the decision procedures to run during
type-checking; the heavy decisions (`⊆ᵈ-dec`{.AgdaFunction} inside
`snow`{.AgdaFunction}) stay unevaluated because every proof below is by
containment reasoning and antisymmetry, never by normalization.

```agda
  module Assembly
    (𝑳          : FiniteLattice)
    (γ          : FiniteLattice.Carrier 𝑳 → DecCon 𝑨 0ℓ)
    (γ-mem      : ∀ k → InFilterIdeal (γ k))
    (classify   : (e : DecCon 𝑨 0ℓ) → InFilterIdeal e
                → Σ[ k ∈ FiniteLattice.Carrier 𝑳 ] proj₁ e ≑ proj₁ (γ k))
    (γ-mono     : ∀ k l → γ k ⊆ᵈ γ l → FiniteLattice._∧_ 𝑳 k l ≡ k)
    (γ-reflect  : ∀ k l → FiniteLattice._∧_ 𝑳 k l ≡ k → γ k ⊆ᵈ γ l)
    where

    private
      𝑳₀ = toLattice 𝑳

    open Lattice-Order 𝑳₀ using ( ≤-antisym )
```

The two maps: classify the restriction; lift the listed member.

```agda
    to₀ : DecCon 𝑩 0ℓ → FiniteLattice.Carrier 𝑳
    to₀ d = proj₁ (classify (restrictᵈ d) (snow d))

    from₀ : FiniteLattice.Carrier 𝑳 → DecCon 𝑩 0ℓ
    from₀ k = liftᵈ (γ k) (γ-mem k)
```

Monotonicity in both directions, through the family's order agreement; the
round trips, by the classification equalities and antisymmetry.

```agda
    to₀-mono : {d e : DecCon 𝑩 0ℓ} → d ⊆ᵈ e → FiniteLattice._∧_ 𝑳 (to₀ d) (to₀ e) ≡ to₀ d
    to₀-mono {d} {e} d⊆e =
      γ-mono (to₀ d) (to₀ e)
        (λ p → proj₁ (proj₂ (classify (restrictᵈ e) (snow e)))
                 (d⊆e (proj₂ (proj₂ (classify (restrictᵈ d) (snow d))) p)))

    from₀-mono : {k l : FiniteLattice.Carrier 𝑳}
      → FiniteLattice._∧_ 𝑳 k l ≡ k → from₀ k ⊆ᵈ from₀ l
    from₀-mono {k} {l} k≤l = γ-reflect k l k≤l

    to₀∘from₀ : (k : FiniteLattice.Carrier 𝑳) → to₀ (from₀ k) ≡ k
    to₀∘from₀ k = ≤-antisym
      (γ-mono (to₀ (from₀ k)) k (proj₂ (proj₂ (classify (restrictᵈ (from₀ k)) (snow (from₀ k))))))
      (γ-mono k (to₀ (from₀ k)) (proj₁ (proj₂ (classify (restrictᵈ (from₀ k)) (snow (from₀ k))))))

    from₀∘to₀ : (d : DecCon 𝑩 0ℓ) → from₀ (to₀ d) ≑ᵈ d
    from₀∘to₀ d =
        proj₂ (proj₂ (classify (restrictᵈ d) (snow d)))
      , proj₁ (proj₂ (classify (restrictᵈ d) (snow d)))
```

The order isomorphism, and the representability witness once the extended
signature's finiteness data are supplied.

```agda
    filterIdeal-ConIsoᵈ : ConIsoᵈ 𝑩 𝑳₀
    filterIdeal-ConIsoᵈ = record
      { to         = to₀
      ; from       = from₀
      ; to-mono    = λ {d} {e} → to₀-mono {d} {e}
      ; from-mono  = λ {k} {l} → from₀-mono {k} {l}
      ; to∘from    = to₀∘from₀
      ; from∘to    = from₀∘to₀
      }

    -- Snow's filter-ideal lemma, packaged: the sublattice α↑ ∪ β↓ is
    -- decidably representable, witnessed by the extended algebra.
    filterIdeal-Representableᵈ : FiniteSignature 𝑆⁺ → Representableᵈ 𝑳₀
    filterIdeal-Representableᵈ fs = record
      { sigᵈ      = 𝑆⁺
      ; algᵈ      = 𝑩
      ; finiteᵈ   = 𝑩-FiniteAlgebra
      ; finsigᵈ   = fs
      ; con-isoᵈ  = filterIdeal-ConIsoᵈ
      }
```

#### Finiteness of the extended signature

The extension adds `n³` unary symbols to a finite finitary signature, so it is
finite finitary whenever the carrier has an `≡`-surjective enumeration (per
the caveat of [Classical.Signatures.Finite][], the *raw* carrier — the setoid
enumeration of a `FiniteAlgebra`{.AgdaRecord} does not suffice).  The
enumeration of the symbol sum and of the triples is assembled from the
standard `Fin`{.AgdaDatatype} splitting and pairing combinators.

```agda
  private
    -- ≡-surjective enumeration of a pair type from ones of the components.
    pairEnum :  {A B : Type 0ℓ} {m n : ℕ}
      →         (Fin m → A) → (Fin n → B) → Fin (m * n) → A × B
    pairEnum {m = m} {n = n} eA eB k =
      eA (proj₁ (remQuot {m} n k)) , eB (proj₂ (remQuot {m} n k))

    pairEnum-sur :  {A B : Type 0ℓ} {m n : ℕ}
                    (eA : Fin m → A) (eB : Fin n → B)
      →             (∀ a → ∃[ i ] eA i ≡ a) → (∀ b → ∃[ j ] eB j ≡ b)
      →             (p : A × B) → ∃[ k ] pairEnum eA eB k ≡ p
    pairEnum-sur {n = n} eA eB eA-sur eB-sur (a , b) with eA-sur a | eB-sur b
    ... | i , ea | j , eb =
      combine i j
      , trans  (cong (λ q → eA (proj₁ q) , eB (proj₂ q)) (remQuot-combine i j))
               (cong₂ _,_ ea eb)

    -- ≡-surjective enumeration of a sum type from ones of the summands.
    sumEnum :  {A B : Type 0ℓ} {m n : ℕ}
      →        (Fin m → A) → (Fin n → B) → Fin (m + n) → A ⊎ B
    sumEnum {m = m} eA eB k = ⊎-map eA eB (splitAt m k)

    sumEnum-sur :  {A B : Type 0ℓ} {m n : ℕ}
                   (eA : Fin m → A) (eB : Fin n → B)
      →            (∀ a → ∃[ i ] eA i ≡ a) → (∀ b → ∃[ j ] eB j ≡ b)
      →            (s : A ⊎ B) → ∃[ k ] sumEnum eA eB k ≡ s
    sumEnum-sur {m = m} {n = n} eA eB eA-sur eB-sur (inj₁ a) with eA-sur a
    ... | i , ea = (i ↑ˡ n) , trans (cong (⊎-map eA eB) (splitAt-↑ˡ m i n)) (cong inj₁ ea)
    sumEnum-sur {m = m} {n = n} eA eB eA-sur eB-sur (inj₂ b) with eB-sur b
    ... | j , eb = (m ↑ʳ j) , trans (cong (⊎-map eA eB) (splitAt-↑ʳ m n j)) (cong inj₂ eb)

  open FiniteSignature

  -- The extended signature is finite finitary, given an ≡-surjective carrier
  -- enumeration.
  𝑆⁺-FiniteSignature :  FiniteSignature 𝑆
    →                   (n : ℕ) (e : Fin n → X) (e-sur : ∀ x → ∃[ i ] e i ≡ x)
    →                   FiniteSignature 𝑆⁺
  𝑆⁺-FiniteSignature 𝑺 n e e-sur .opCard = 𝑺 .opCard + n * (n * n)
  𝑆⁺-FiniteSignature 𝑺 n e e-sur .opEnum =
    sumEnum (𝑺 .opEnum) (pairEnum e (pairEnum e e))
  𝑆⁺-FiniteSignature 𝑺 n e e-sur .opEnum-sur =
    sumEnum-sur  (𝑺 .opEnum) (pairEnum e (pairEnum e e)) (𝑺 .opEnum-sur)
                 (pairEnum-sur e (pairEnum e e) e-sur (pairEnum-sur e e e-sur e-sur))
  𝑆⁺-FiniteSignature 𝑺 n e e-sur .finitary (inj₁ f)  = 𝑺 .finitary f
  𝑆⁺-FiniteSignature 𝑺 n e e-sur .finitary (inj₂ _)  = 1 , ↔-id _
```

--------------------------------------
