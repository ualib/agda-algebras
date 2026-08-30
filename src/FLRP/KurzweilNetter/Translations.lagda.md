---
layout: default
file: "src/FLRP/KurzweilNetter/Translations.lagda.md"
title: "FLRP.KurzweilNetter.Translations module (The Agda Universal Algebra Library)"
date: "2026-07-28"
author: "the agda-algebras development team"
---

### Basic translations, and the invariant partitions of a finite algebra

This is the [FLRP.KurzweilNetter.Translations][] module of the [Agda Universal Algebra Library][].

The manuscript proof of Kurzweil–Netter duality[^1] opens by assuming the
representing algebra has *unary* operations, citing the unary-reduction theorem
`Con 𝑨 = Con ⟨A , Pol₁ 𝑨⟩` which is not yet formalized in the library.  The
construction in this module lifts only the **basic translations** of
`𝑨`{.AgdaBound}, that is, the unary maps obtained from one basic operation by
fixing all argument positions but one, and the classical Mal'cev-style observation
that these already determine the congruences.

+  Every congruence partition is invariant under every basic translation
   (`pvOf-invariant`{.AgdaFunction}, one appeal to compatibility); and, conversely,

+  a partition invariant under all basic translations induces a relation
   compatible with every operation of every arity
   (`blockRel-compatible`{.AgdaFunction}); this is the **translation criterion**,
   proved by walking the argument tuple one position at a time and using one
   translation instance per step.

This is exactly the interface the expansion step consumes: the operations lifted
to the coset algebra in [FLRP.KurzweilNetter.Expansion][] are unary maps of the
index set, and a family of unary index maps is precisely what this module
produces.

**Presentation of the translations**.  The carrier is presented by an
irredundant enumeration `ienum[_] : Fin m → 𝕌[ 𝑨 ]`
([Setoid.Algebras.Finite.Irredundant][]), so a translation is presented as a map
`Fin m → Fin m`: feed the moving index and the constants to the operation through
`ienum[_]`{.AgdaFunction}, and take the index of the result.  A translation datum
`TrData`{.AgdaFunction} records an operation symbol (through the symbol
enumeration of the `FiniteSignature`{.AgdaRecord}), a distinguished argument
position, and the constant tuple *positionally encoded* as a single
`Fin (m ^ k)`{.AgdaDatatype} via the standard library's `finToFun`{.AgdaFunction},
encoded rather than functional so that downstream the family can be *flatly indexed*
by `Fin trCount`{.AgdaDatatype} (`trFamily`{.AgdaFunction} below), which is the
shape the expanded algebra's finite signature needs.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module FLRP.KurzweilNetter.Translations where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                                 using  ( if_then_else_ )
open import Data.Empty                                     using  ( ⊥-elim )
open import Data.Fin.Base                                  using  ( Fin ; funToFin
                                                                  ; fromℕ< ; toℕ
                                                                  ; finToFun )
open import Data.Fin.Properties                            using  ( toℕ<n ; toℕ-fromℕ<
                                                                  ; toℕ-injective
                                                                  ; finToFun-funToFin )
                                                           renaming ( _≟_ to _≟ᶠ_ )
open import Data.List.Base                                 using  ( List ; length
                                                                  ; lookup ; concatMap
                                                                  ; cartesianProduct
                                                                  ; allFin )
                                                           renaming ( map to lmap )
open import Data.List.Membership.Propositional             using  ( _∈_ )
open import Data.List.Membership.Propositional.Properties  using  ( ∈-allFin ; ∈-map⁺
                                                                  ; ∈-cartesianProduct⁺
                                                                  ; ∈-concat⁺′ )
open import Data.List.Relation.Unary.Any                   using  ( index )
open import Data.List.Relation.Unary.Any.Properties        using  ( lookup-index )
open import Data.Nat.Base                                  using  ( ℕ ; zero ; suc
                                                                  ; _≤_ ; _<_ ; s≤s )
                                                           renaming ( _^_ to _^ᴺ_ )
open import Data.Nat.Properties                            using  ( _<?_ ; ≤-refl
                                                                  ; ≤-trans ; n≤1+n
                                                                  ; <-irrefl ; ≤∧≢⇒< )
open import Data.Product                                   using  ( Σ-syntax ; _×_
                                                                  ; _,_ ; proj₁ ; proj₂ )
open import Function                                       using  ( Func ; Inverse )
open import Level                                          using  ( 0ℓ )
open import Relation.Binary                                using  ( Setoid
                                                                  ; IsEquivalence )
open import Relation.Binary.PropositionalEquality          using  ( _≡_ ; refl ; sym
                                                                  ; trans ; cong
                                                                  ; subst ; subst₂ )
open import Relation.Nullary                               using  ( ¬_ ; Dec ; yes ; no )
open import Relation.Nullary.Decidable                     using  ( does ; dec-true
                                                                  ; dec-false )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Partitions        using  ( SameBlock )
open import FLRP.KurzweilNetter.Blocks                     using  ( module KNBlocks )
open import FLRP.KurzweilNetter.Invariance                 using  ( Inv )
open import Overture                                       using  ( Signature
                                                                  ; OperationSymbolsOf
                                                                  ; _|:_ ; ArityOf)
open import Setoid.Algebras.Basic                          using  ( Algebra ; 𝕌[_]
                                                                  ; 𝔻[_] ; _^_ )
open import Setoid.Algebras.Finite.Irredundant             using  ( IrredundantEnumeration )
open import Setoid.Congruences.Basic                       using  ( _∣≈_ ; mkcon ; reflexive
                                                                  ; is-equivalence
                                                                  ; is-compatible )
open import Setoid.Congruences.Certificates.Schema         using  ( ParentVec )
open import Setoid.Congruences.Finite.Basic                using  ( DecCon )
open import Setoid.Signatures.Finite                       using  ( FiniteSignature )

open Algebra using ( Interp )
```
-->

#### The translation toolkit

`KNTranslations`{.AgdaModule} fixes the finite finitary algebra, through its
signature-finiteness witness, and an irredundant enumeration of its carrier,
and opens the relation-level dictionary of [FLRP.KurzweilNetter.Blocks][].

```agda
module KNTranslations  {𝑆 : Signature 0ℓ 0ℓ} (𝑨 : Algebra {𝑆 = 𝑆} 0ℓ 0ℓ)
                       (𝑺 : FiniteSignature 𝑆) (𝑬 : IrredundantEnumeration 𝑨) where

  open KNBlocks 𝑨 𝑬
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming  ( refl to ≈refl ; sym to ≈sym
                                              ; trans to ≈trans ; reflexive to ≈reflexive )

  open IrredundantEnumeration 𝑬 using ( ienum[_] ) renaming ( icard to m )
  open FiniteSignature 𝑺 using  ( opCard ; opEnum ; opEnum-sur ; arCard ; arIdx
                                ; arEnum ; arEnum-arIdx ; finitary )

  private
    -- The other round trip of the arity bijection (the record exposes only
    -- arEnum-arIdx; this direction is read off the underlying Inverse).
    arIdx-arEnum : (f : OperationSymbolsOf 𝑆) (q : Fin (arCard f)) → arIdx f (arEnum f q) ≡ q
    arIdx-arEnum f = Inverse.strictlyInverseˡ (finitary f .proj₂)

    -- Congruence of an operation application in its argument tuple.
    fcong : (f : OperationSymbolsOf 𝑆) {u v : ArityOf 𝑆 f → 𝕌[ 𝑨 ]}
      → (∀ a → u a ≈ v a) → (f ^ 𝑨) u ≈ (f ^ 𝑨) v
    fcong f h = Func.cong (Interp 𝑨) (refl , h)
```

#### Translation data and the presented index maps

A translation datum is an operation symbol (as an index into the symbol enumeration),
a distinguished argument position, and a positional encoding of the constants at
the remaining positions.  A nullary operation contributes no data (its position
type is empty), matching the mathematics: constants impose no congruence constraint.

```agda
  -- One basic-translation instance, as pure data.
  TrData : Type 0ℓ
  TrData = Σ[ o ∈ Fin opCard ] (Fin (arCard (opEnum o)) × Fin (m ^ᴺ arCard (opEnum o)))

  private
    -- The index tuple fed to the operation: the moving index at the
    -- distinguished position, the decoded constants elsewhere.
    mixIx : {k : ℕ} → Fin k → Fin (m ^ᴺ k) → Fin m → Fin k → Fin m
    mixIx p cc i q = if does (q ≟ᶠ p) then i else finToFun cc q

  -- The unary index map presented by a translation datum.
  trMapOf : TrData → Fin m → Fin m
  trMapOf (o , p , cc) i =
    eIdx ((opEnum o ^ 𝑨) λ a → ienum[ mixIx p cc i (arIdx (opEnum o) a) ])
```

#### Soundness: congruence partitions are invariant

The partition of a decidable congruence is invariant under every translation:
the moving position carries the related pair, the constant positions carry
reflexivity, and compatibility of the congruence does the rest.

```agda
  -- The partition of a decidable congruence is invariant under every translation.
  pvOf-invariant : (d : DecCon 𝑨 0ℓ) (td : TrData) → Inv (trMapOf td) (pvOf d)
  pvOf-invariant d@((_θ_ , θcon) , _) (o , p , cc) {i} {j} sb = pvOf-complete d related
    where
    θ-refl≈  = reflexive θcon
    θ-sym    = IsEquivalence.sym (is-equivalence θcon)
    θ-trans  = IsEquivalence.trans (is-equivalence θcon)

    f = opEnum o

    -- the two argument tuples, and their pointwise relatedness
    argsAt : Fin m → ArityOf 𝑆 f → 𝕌[ 𝑨 ]
    argsAt i' a = ienum[ mixIx p cc i' (arIdx f a) ]

    mixRel : (q : Fin (arCard f)) (dq : Dec (q ≡ p))
      → ienum[ if does dq then i else finToFun cc q ]
        θ ienum[ if does dq then j else finToFun cc q ]
    mixRel q (yes _)  = pvOf-sound d sb
    mixRel q (no _)   = θ-refl≈ ≈refl

    relF : (f ^ 𝑨)(argsAt i) θ (f ^ 𝑨)(argsAt j)
    relF = is-compatible θcon f λ a → mixRel (arIdx f a) (arIdx f a ≟ᶠ p)

    related : ienum[ trMapOf (o , p , cc) i ] θ ienum[ trMapOf (o , p , cc) j ]
    related = θ-trans (θ-refl≈ (eIdx-≈ ((f ^ 𝑨) (argsAt i))))
                (θ-trans relF (θ-sym (θ-refl≈ (eIdx-≈ ((f ^ 𝑨) (argsAt j))))))
```

#### The translation criterion

Conversely, a partition invariant under every translation induces a relation
compatible with every operation.  The proof is the classical one-position walk:
to relate `f u` and `f v` for pointwise-related tuples, pass through the
hybrids `hyb l` that take `v`-values at positions below `l` and `u`-values at
the rest; consecutive hybrids differ in one position, which is one invariance
instance, with the constants of the instance encoding the current hybrid.

```agda
  -- The translation criterion: a partition invariant under every translation
  -- induces a relation compatible with every operation of 𝑨.
  blockRel-compatible : (pv : ParentVec m)
    → ((td : TrData) → Inv (trMapOf td) pv) → 𝑨 ∣≈ blockRel pv
  blockRel-compatible pv inv 𝑓 =
    subst  (λ g → (g ^ 𝑨) |: blockRel pv) (opEnum-sur 𝑓 .proj₂)
           (compatAt (opEnum-sur 𝑓 .proj₁))
    where
    compatAt : (o : Fin opCard) → (opEnum o ^ 𝑨) |: blockRel pv
    compatAt o {u} {v} hyp = final
      where
      f = opEnum o
      k = arCard f

      -- the hybrid tuples: v-values strictly below the threshold, u-values above
      hyb : ℕ → ArityOf 𝑆 f → 𝕌[ 𝑨 ]
      hyb l a = if does (toℕ (arIdx f a) <? l) then v a else u a

      -- boundary identifications
      hyb0≈u : ∀ a → hyb 0 a ≈ u a
      hyb0≈u a = ≈reflexive
        (cong (λ b → if b then v a else u a) (dec-false (toℕ (arIdx f a) <? 0) λ ()))

      hybk≈v : ∀ a → hyb k a ≈ v a
      hybk≈v a =
        ≈reflexive (cong  (λ b → if b then v a else u a)
                          (dec-true (toℕ (arIdx f a) <? k) (toℕ<n (arIdx f a))))

      -- one step of the walk: position l moves from its u-value to its v-value
      step : (l : ℕ) (sl≤k : suc l ≤ k)
        → blockRel pv ((f ^ 𝑨)(hyb l)) ((f ^ 𝑨)(hyb (suc l)))
      step l sl≤k =
        subst₂ (SameBlock pv) tI≡ tJ≡ (inv (o , pl , cc) (hyp p))
        where
        pl : Fin k
        pl = fromℕ< sl≤k

        p : ArityOf 𝑆 f
        p = arEnum f pl

        -- the constants encode the current hybrid
        cc : Fin (m ^ᴺ k)
        cc = funToFin (λ q → eIdx (hyb l (arEnum f q)))

        toℕpl : toℕ pl ≡ l
        toℕpl = toℕ-fromℕ< sl≤k

        -- the distinguished position is not yet moved in hyb l ...
        arIdx-p : arIdx f p ≡ pl
        arIdx-p = arIdx-arEnum f pl

        hybl-p : hyb l p ≡ u p
        hybl-p = cong (λ b → if b then v p else u p)
          (dec-false (toℕ (arIdx f p) <? l)
            (λ lt → <-irrefl refl (subst (_< l) (trans (cong toℕ arIdx-p) toℕpl) lt)))

        -- ... and is moved in hyb (suc l)
        hybsl-p : hyb (suc l) p ≡ v p
        hybsl-p = cong (λ b → if b then v p else u p)
          (dec-true (toℕ (arIdx f p) <? suc l)
            (subst (_< suc l) (sym (trans (cong toℕ arIdx-p) toℕpl)) ≤-refl))

        -- away from the distinguished position the two hybrids agree
        hyb-stable : (q : Fin k) → ¬ (q ≡ pl)
          → hyb l (arEnum f q) ≡ hyb (suc l) (arEnum f q)
        hyb-stable q ne =
          stable (toℕ (arIdx f (arEnum f q)) <? l) (toℕ (arIdx f (arEnum f q)) <? suc l)
          where
          a' = arEnum f q

          x≢l : ¬ (toℕ (arIdx f a') ≡ l)
          x≢l xl = ne (toℕ-injective
            (trans (trans (sym (cong toℕ (arIdx-arEnum f q))) xl) (sym toℕpl)))

          stable : (d₁ : Dec (toℕ (arIdx f a') < l)) (d₂ : Dec (toℕ (arIdx f a') < suc l))
            → (if does d₁ then v a' else u a') ≡ (if does d₂ then v a' else u a')
          stable (yes _)   (yes _)   = refl
          stable (no _)    (no _)    = refl
          stable (yes lt)  (no nlt)  = ⊥-elim (nlt (≤-trans lt (n≤1+n l)))
          stable (no nlt)  (yes lt)  = ⊥-elim (nlt (≤∧≢⇒< (pred≤ lt) x≢l))
            where
            pred≤ : suc (toℕ (arIdx f a')) ≤ suc l → toℕ (arIdx f a') ≤ l
            pred≤ (s≤s le) = le

        -- the translation at the moving u-index computes hyb l ...
        keyU : (q : Fin k) (dq : Dec (q ≡ pl))
          → ienum[ if does dq then eIdx (u p) else finToFun cc q ] ≈ hyb l (arEnum f q)
        keyU q (yes e) = ≈trans (eIdx-≈ (u p))
          (≈reflexive (sym (trans (cong (hyb l) (cong (arEnum f) e)) hybl-p)))
        keyU q (no _)  = ≈trans
          (≈reflexive (cong ienum[_] (finToFun-funToFin (λ q' → eIdx (hyb l (arEnum f q'))) q)))
          (eIdx-≈ (hyb l (arEnum f q)))

        -- ... and at the moving v-index computes hyb (suc l)
        keyV : (q : Fin k) (dq : Dec (q ≡ pl))
          → ienum[ if does dq then eIdx (v p) else finToFun cc q ] ≈ hyb (suc l) (arEnum f q)
        keyV q (yes e) = ≈trans (eIdx-≈ (v p))
          (≈reflexive (sym (trans (cong (hyb (suc l)) (cong (arEnum f) e)) hybsl-p)))
        keyV q (no ne) = ≈trans
          (≈reflexive (cong ienum[_] (finToFun-funToFin (λ q' → eIdx (hyb l (arEnum f q'))) q)))
          (≈trans (eIdx-≈ (hyb l (arEnum f q))) (≈reflexive (hyb-stable q ne)))

        argU : ∀ a → ienum[ mixIx pl cc (eIdx (u p)) (arIdx f a) ] ≈ hyb l a
        argU a = ≈trans (keyU (arIdx f a) (arIdx f a ≟ᶠ pl))
                        (≈reflexive (cong (hyb l) (arEnum-arIdx f a)))

        argV : ∀ a → ienum[ mixIx pl cc (eIdx (v p)) (arIdx f a) ] ≈ hyb (suc l) a
        argV a = ≈trans (keyV (arIdx f a) (arIdx f a ≟ᶠ pl))
                        (≈reflexive (cong (hyb (suc l)) (arEnum-arIdx f a)))

        tI≡ : trMapOf (o , pl , cc) (eIdx (u p)) ≡ eIdx ((f ^ 𝑨) (hyb l))
        tI≡ = eIdx-cong (fcong f argU)

        tJ≡ : trMapOf (o , pl , cc) (eIdx (v p)) ≡ eIdx ((f ^ 𝑨) (hyb (suc l)))
        tJ≡ = eIdx-cong (fcong f argV)

      -- the walk accumulates the steps from the all-u tuple ...
      walk : (l : ℕ) → l ≤ k → blockRel pv ((f ^ 𝑨) u) ((f ^ 𝑨) (hyb l))
      walk zero     _     = blockRel-refl≈ pv (fcong f (λ a → ≈sym (hyb0≈u a)))
      walk (suc l)  sl≤k  = trans (walk l (≤-trans (n≤1+n l) sl≤k)) (step l sl≤k)

      -- ... and lands on the all-v tuple
      final : blockRel pv ((f ^ 𝑨) u) ((f ^ 𝑨) v)
      final = trans (walk k ≤-refl) (blockRel-refl≈ pv (fcong f hybk≈v))
```

A partition invariant under every translation therefore presents a decidable
congruence: the relation, its equivalence laws, its compatibility from the
criterion, and its decision procedure by label comparison.

```agda
  -- The decidable congruence presented by an invariant partition.
  blockCon : (pv : ParentVec m) → ((td : TrData) → Inv (trMapOf td) pv) → DecCon 𝑨 0ℓ
  blockCon pv inv =
    ( blockRel pv
    , mkcon (blockRel-refl≈ pv) (blockRel-isEquivalence pv) (blockRel-compatible pv inv) )
    , blockRel-dec pv
```

#### The flat family

The expansion step ([FLRP.KurzweilNetter.Expansion][]) consumes the translations
as a family indexed by a plain `Fin`{.AgdaDatatype}, which is the shape a finite
signature's symbol type needs.  The family is obtained by listing all translation
data (finitely many: symbols, positions, and constant codes are all enumerated)
and reading the list back through positional lookup; completeness of the listing
is what converts family-invariance back into invariance under every datum.

```agda
  private
    blockOf : Fin opCard → List TrData
    blockOf o = lmap (o ,_)
      (cartesianProduct (allFin (arCard (opEnum o))) (allFin (m ^ᴺ arCard (opEnum o))))

    trList : List TrData
    trList = concatMap blockOf (allFin opCard)

    trList-complete : (td : TrData) → td ∈ trList
    trList-complete (o , p , cc) =
      ∈-concat⁺′
        (∈-map⁺ (o ,_) (∈-cartesianProduct⁺ (∈-allFin p) (∈-allFin cc)))
        (∈-map⁺ blockOf (∈-allFin o))

  -- The number of translation instances.
  trCount : ℕ
  trCount = length trList

  -- The translation datum at a flat index.
  trIdx : Fin trCount → TrData
  trIdx = lookup trList

  -- Every translation datum occurs at some flat index.
  trIdx-complete : (td : TrData) → Σ[ τ ∈ Fin trCount ] trIdx τ ≡ td
  trIdx-complete td = index mem , sym (lookup-index mem)
    where
    mem : td ∈ trList
    mem = trList-complete td

  -- The flatly indexed translation family.
  trFamily : Fin trCount → Fin m → Fin m
  trFamily τ = trMapOf (trIdx τ)
```

The two facing consequences, in the exact shapes the duality proof consumes:
congruence partitions are invariant under the whole family, and
family-invariance suffices for the criterion.

```agda
  -- Congruence partitions are invariant under the whole family.
  pvOf-invariant-family : (d : DecCon 𝑨 0ℓ) (τ : Fin trCount)
    → Inv (trFamily τ) (pvOf d)
  pvOf-invariant-family d τ = pvOf-invariant d (trIdx τ)

  -- Family invariance covers every translation datum.
  family-invariant-all : (pv : ParentVec m)
    → ((τ : Fin trCount) → Inv (trFamily τ) pv)
    → (td : TrData) → Inv (trMapOf td) pv
  family-invariant-all pv h td =
    subst (λ z → Inv (trMapOf z) pv) (trIdx-complete td .proj₂)
          (h (trIdx-complete td .proj₁))

  -- The decidable congruence presented by a family-invariant partition.
  blockConᶠ : (pv : ParentVec m)
    → ((τ : Fin trCount) → Inv (trFamily τ) pv) → DecCon 𝑨 0ℓ
  blockConᶠ pv h = blockCon pv (family-invariant-all pv h)
```

--------------------------------------

[^1]: See `docs/papers/fin-lat-rep/SmallLatticeReps.tex` § "Lattice duals".
