---
layout: default
file: "src/Setoid/Congruences/Certificates/Congruence.lagda.md"
title: "Setoid.Congruences.Certificates.Congruence module (The Agda Universal Algebra Library)"
date: "2026-07-22"
author: "the agda-algebras development team"
---

### The per-congruence certificate checker (obligations C1–C3)

This is the [Setoid.Congruences.Certificates.Congruence][] module of the [Agda Universal Algebra Library][].

Fix a finite finitary algebra — an algebra `𝑨` with carrier-finiteness data
`𝑭` ([Setoid.Algebras.Finite][]) and signature-finiteness data `𝑺`
([Setoid.Signatures.Finite][]).  A per-congruence certificate
(`CgCert`{.AgdaRecord} of [Setoid.Congruences.Certificates.Schema][]) claims

> the partition presented by the parent vector  `≑  Cg (fromPairs P)`

for its seed list `P`.

This module is the checker for that claim.  The *claimed congruence* is the *table
relation* of the parent vector: two carrier elements are related when their
enumeration indices have the same parent — two constant-time lookups and one
`Fin`{.AgdaDatatype} equality, so the relation is decidable with no appeal to the
specification-grade decision procedure `Cg-dec`{.AgdaFunction},[^1]
which never appears here.

The checker obligations of
[the design note](docs/notes/flrp-wp6-freese-certificates.md),
each search-free and linear in the trace and table size, are as follows:

+  **C1 (trace soundness)**.  Every merge of the Freese trace is derivable:
   seed entries point into `P`, and translate entries apply one
   `compatible`{.AgdaInductiveConstructor} rule of the generation datatype
   `Gen`{.AgdaDatatype} ([Setoid.Congruences.Generation][]) to an earlier merge.
   The checker *constructs* the `Gen`{.AgdaDatatype} derivations by a single
   fold over the trace — it never decides `Gen`{.AgdaDatatype}-membership.
+  **C2 (claimed ⊆ generated)**.  The design note offered two implementations
   and defaulted to (a), checking each forest edge of the claimed vector for
   membership in the trace's merged pairs.  Implementing against honest `cg2`
   traces shows option (a) as literally stated is unattainable: the run's merged
   pairs need not contain the *normal-form* edges, because normal form re-roots
   every block at its least element after the run.  We therefore implement the
   note's sanctioned option (b) in its simplest form: **replay** the trace's
   unions through an eager re-pointing root vector — no ranks, no path
   compression; those are engine-side devices — carrying a
   `Gen`{.AgdaDatatype}-proof invariant, and then align the replayed partition
   with the claimed vector by two linear sweeps (`Covers`{.AgdaFunction}).
   Cost: `O(n · |trace|)` root updates, one pass, no search.
+  **C3 (generated ⊆ claimed)**.  The claimed partition contains the seed pairs
   (`Respects`{.AgdaFunction}) and is a congruence: as a partition it is an
   equivalence for free, and operation-compatibility is checked on **one
   translate step per coordinate per tuple** (`EdgeCompat`{.AgdaFunction}) —
   the pair `(t , t [ c ]≔ parent (t c))` for every basic operation, coordinate,
   and argument tuple, which is Freese's `O(r · ‖A‖)` bound of unary polynomial
   translates times forest edges.  Compatibility for arbitrary pointwise-related
   tuples then follows by walking the coordinates and detouring through the
   roots, with no further checking.  `Cg-least`{.AgdaFunction} closes the
   inclusion.

The headline theorems `table≑Cg`{.AgdaFunction} (with a trace) and
`table≑CgEdges`{.AgdaFunction} (the trace-free special case where the seeds are
the vector's own forest edges, used for whole-lattice congruence lists) deliver
the claim as an honest `_≑_`{.AgdaFunction} at the working congruence level.

Every hypothesis is decidable, and each decider is a bounded sweep of
`Fin`{.AgdaDatatype} comparisons; the whole-lattice checker
([Setoid.Congruences.Certificates.Lattice][]) instantiates them wholesale.

<!--
```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Setoid.Congruences.Certificates.Congruence where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Bool.Base        using  ( if_then_else_ )
open import Data.Empty            using  ( ⊥ )
open import Data.Fin.Base         using  ( Fin )
open import Data.Fin.Properties   using  ( all? ) renaming ( _≟_ to _≟ᶠ_ )
open import Data.List.Base        using  ( List ; [] ; _∷_ ; map ; filter
                                         ; allFin ; foldr )
open import Data.List.Membership.Propositional
                                  using  ( _∈_ ; lose )
open import Data.List.Membership.Propositional.Properties
                                  using  ( ∈-map⁺ ; ∈-filter⁺ ; ∈-allFin )
open import Data.List.Relation.Unary.Any
                                  using  ( here ; there )
open import Data.List.Relation.Unary.All
                                  using  ( All ; [] ; _∷_ ; lookupAny ; universal )
                                  renaming ( map to all-map ; lookup to all-lookup
                                           ; all? to allL? )
open import Data.List.Relation.Unary.All.Properties
                                  using  ( map⁺ )
open import Data.Nat.Base         using  ( ℕ ; zero ; suc )
open import Data.Product          using  ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Base        using  ( ⊤ ; tt )
open import Data.Vec.Base         using  ( Vec ; lookup ; tabulate ; _[_]≔_ )
                                  renaming ( map to mapᵥ )
open import Data.Vec.Properties   using  ( lookup∘tabulate ; lookup∘update
                                         ; lookup∘update′ ; []≔-idempotent
                                         ; []≔-lookup ; lookup-map )
open import Function              using  ( Func )
open import Level                 using  ( Level ; _⊔_ ; Lift ; lift ; lower )
open import Relation.Binary       using  ( Setoid ) renaming ( Rel to BinaryRel )
open import Relation.Binary.PropositionalEquality
                                  using  ( _≡_ ; refl ; sym ; trans ; cong
                                         ; subst ; subst₂ )
open import Relation.Nullary.Decidable
                                  using  ( Dec ; yes ; no ; does ; map′
                                         ; _×-dec_ ; _→-dec_ ; ¬? )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                                using  ( 𝓞 ; 𝓥 ; Signature
                                                           ; OperationSymbolsOf
                                                           ; ArityOf )
open import Setoid.Algebras.Basic                   using  ( Algebra ; 𝕌[_]
                                                           ; 𝔻[_] ; _^_ )
open import Setoid.Algebras.Finite                  using  ( FiniteAlgebra )
open import Setoid.Congruences.Basic                using  ( Con ; mkcon ; _∣≈_ )
open import Setoid.Congruences.Finite.Basic         using  ( DecCon )
open import Setoid.Congruences.Generation           using  ( Gen ; Cg ; base ; rfl
                                                           ; symmetric ; transitive
                                                           ; compatible ; Cg-least )
open import Setoid.Congruences.Lattice              using  ( _≑_ )
open import Setoid.Congruences.Presented            using  ( fromPairs ; allVecs
                                                           ; ∈-allVecs )
open import Setoid.Congruences.Certificates.Schema  using  ( ParentVec ; parent
                                                           ; IdempotentParent
                                                           ; forestEdges
                                                           ; Justification ; seed
                                                           ; translate ; Merge
                                                           ; mkMerge ; Trace
                                                           ; CgCert )
open import Setoid.Signatures.Finite                using  ( FiniteSignature )

private variable α ρ : Level
```
-->

#### Positional predicates

Trace justifications refer to seed pairs and earlier merges by position.
`AtPos P xs k`{.AgdaFunction} asserts that the element at position `k` of `xs`
exists and satisfies `P` — by recursion on the list, with the out-of-range case
uninhabited, so an invalid reference *is* a failed check rather than a partial
lookup.  `atPos?`{.AgdaFunction} decides it, and `atPos-use`{.AgdaFunction}
consumes it against an `All`{.AgdaDatatype}-package of facts about the same
list (the checker's accumulated `Gen`{.AgdaDatatype} proofs).

```agda
-- The element at position k exists and satisfies P.
AtPos : {a p : Level} {A : Type a} (P : A → Type p) → List A → ℕ → Type p
AtPos {p = p} P []  _        = Lift p ⊥
AtPos P (x ∷ xs)    zero     = P x
AtPos P (x ∷ xs)    (suc k)  = AtPos P xs k

-- AtPos is decidable when P is.
atPos? : {a p : Level} {A : Type a} {P : A → Type p}
  →  ((x : A) → Dec (P x)) → (xs : List A) (k : ℕ) → Dec (AtPos P xs k)
atPos? P? []        k        = no (λ { (lift ()) })
atPos? P? (x ∷ xs)  zero     = P? x
atPos? P? (x ∷ xs)  (suc k)  = atPos? P? xs k

-- Consume a positional fact together with the All-fact at the same position.
atPos-use : {a p q c : Level} {A : Type a}
  {P : A → Type p} {Q : A → Type q} {C : Type c}
  →  (xs : List A) (k : ℕ) → All Q xs → AtPos P xs k
  →  ((x : A) → Q x → P x → C) → C
atPos-use []        k        _           (lift ())
atPos-use (x ∷ xs)  zero     (qx ∷ _)    px  use = use x qx px
atPos-use (x ∷ xs)  (suc k)  (_ ∷ qxs)   pk  use = atPos-use xs k qxs pk use
```

#### The ambient finite finitary algebra

Everything below lives in the named module `CertCheck 𝑭 𝑺`{.AgdaModule},
parameterized by carrier-finiteness data `𝑭` and signature-finiteness data `𝑺`,
so that downstream checkers (and emitted certificate modules) bring the whole
interface into scope with one `open`{.AgdaKeyword}.  As in
[Setoid.Congruences.Presented][], `idx` is a chosen enumeration index for each
carrier element.  `arOf`{.AgdaFunction}
is the arity table against which certificate literals type-check (for concrete
signatures it reduces definitionally), `carrierPairs`{.AgdaFunction} reads an
index-pair list back into the carrier, and `appIdx`{.AgdaFunction} is the
index-level view of one basic-operation application: decode the index tuple,
apply the operation, re-encode.

```agda
module CertCheck {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ}
                 (𝑭 : FiniteAlgebra 𝑨) (𝑺 : FiniteSignature 𝑆) where

  open FiniteAlgebra 𝑭 using ( _≟_ ; card ; enum ; enum-sur )
  open FiniteSignature 𝑺 using ( opCard ; opEnum ; opEnum-sur
                               ; arCard ; arEnum ; arIdx ; arEnum-arIdx )
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
    renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans
             ; reflexive to ≈reflexive )

  private
    -- A chosen enumeration index for each carrier element, and its correctness.
    idx : 𝕌[ 𝑨 ] → Fin card
    idx x = proj₁ (enum-sur x)

    idx-≈ : (x : 𝕌[ 𝑨 ]) → enum (idx x) ≈ x
    idx-≈ x = proj₂ (enum-sur x)

  -- Pairs of enumeration indices: the index-level currency of certificates.
  IdxPair : Type
  IdxPair = Fin card × Fin card

  -- The arity table certificates are checked against.
  arOf : Fin opCard → ℕ
  arOf fi = arCard (opEnum fi)

  -- Reading an index-pair list back into the carrier.
  carrierPairs : List IdxPair → List (𝕌[ 𝑨 ] × 𝕌[ 𝑨 ])
  carrierPairs = map (λ (p₁ , p₂) → enum p₁ , enum p₂)

  -- The carrier tuple encoded by a tuple of carrier indices.
  tupleOf : (fi : Fin opCard)
    → Vec (Fin card) (arOf fi) → (ArityOf 𝑆 (opEnum fi) → 𝕌[ 𝑨 ])
  tupleOf fi t a = enum (lookup t (arIdx (opEnum fi) a))

  -- One basic-operation application, at the index level.
  appIdx : (fi : Fin opCard) → Vec (Fin card) (arOf fi) → Fin card
  appIdx fi t = idx ((opEnum fi ^ 𝑨) (tupleOf fi t))
```

A decidability utility: a universally quantified statement over the index
tuples of one arity is decided by sweeping the tuple enumeration
`allVecs`{.AgdaFunction} of [Setoid.Congruences.Presented][] (whose
completeness `∈-allVecs`{.AgdaFunction} converts the swept
`All`{.AgdaDatatype} back into a Π-statement).

```agda
  -- Decide a Π-statement over index tuples by sweeping the tuple enumeration.
  allVecsΠ? : {p : Level} {k : ℕ} {P : Vec (Fin card) k → Type p}
    →  ((t : Vec (Fin card) k) → Dec (P t)) → Dec (∀ t → P t)
  allVecsΠ? {k = k} {P} P? with allL? P? (allVecs card k)
  ... | yes a  = yes (λ t → all-lookup a (∈-allVecs t))
  ... | no ¬a  = no (λ h → ¬a (universal h (allVecs card k)))
```

#### The claimed partition as a relation

`SameBlock`{.AgdaFunction} is the index-level reading of a parent vector — two
indices related when their parents agree — and `TableRel`{.AgdaFunction} its
carrier-level reading through `idx`, lifted to the working congruence level.

For `TableRel`{.AgdaFunction} to be well defined on the *setoid* carrier the
vector must not distinguish `≈`-equal enumerated elements; that is the
(decidable) `Coherent`{.AgdaFunction} condition, from which respect for `≈`
follows in general (`tableResp-≈`{.AgdaFunction}).

```agda
  -- Two indices lie in the same claimed block.
  SameBlock : ParentVec card → Fin card → Fin card → Type
  SameBlock pv i j = parent pv i ≡ parent pv j

  -- The claimed partition does not distinguish ≈-equal enumerated elements.
  Coherent : ParentVec card → Type ρ
  Coherent pv = ∀ i j → enum i ≈ enum j → SameBlock pv i j

  coherent? : (pv : ParentVec card) → Dec (Coherent pv)
  coherent? pv =
    all? (λ i → all? (λ j → (enum i ≟ enum j) →-dec (parent pv i ≟ᶠ parent pv j)))

  -- The carrier-level relation presented by a parent vector.
  TableRel : ParentVec card → BinaryRel 𝕌[ 𝑨 ] (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  TableRel pv x y = Lift (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ) (SameBlock pv (idx x) (idx y))

  -- The table relation is decidable outright: two lookups and a Fin equality.
  tableDec : (pv : ParentVec card) → ∀ x y → Dec (TableRel pv x y)
  tableDec pv x y = map′ lift lower (parent pv (idx x) ≟ᶠ parent pv (idx y))

  -- ≈-equal elements have same-block indices ...
  sameBlock-resp-≈ : (pv : ParentVec card) → Coherent pv
    →  ∀ {x y} → x ≈ y → SameBlock pv (idx x) (idx y)
  sameBlock-resp-≈ pv coh {x} {y} x≈y =
    coh (idx x) (idx y) (≈trans (idx-≈ x) (≈trans x≈y (≈sym (idx-≈ y))))

  -- ... so the table relation is reflexive over ≈ ...
  tableReflexive : (pv : ParentVec card) → Coherent pv
    →  ∀ {x y} → x ≈ y → TableRel pv x y
  tableReflexive pv coh x≈y = lift (sameBlock-resp-≈ pv coh x≈y)

  -- ... and respects ≈-replacement of related elements.
  tableResp-≈ : (pv : ParentVec card) → Coherent pv
    →  ∀ {x y a b} → x ≈ a → y ≈ b → TableRel pv a b → TableRel pv x y
  tableResp-≈ pv coh x≈a y≈b (lift ab) =
    lift (trans (sameBlock-resp-≈ pv coh x≈a)
                (trans ab (sym (sameBlock-resp-≈ pv coh y≈b))))
```

#### C3, the checked half: one translate step per coordinate

`EdgeCompat`{.AgdaFunction} is the certificate's compatibility obligation: for
every enumerated operation symbol, coordinate, and index tuple, replacing the
coordinate's entry by its *root* stays in the same claimed block.  These are
exactly Freese's unary polynomial translates applied to the forest edges
`(i , parent i)` (a root entry makes the statement trivially reflexive), so the
sweep is linear in the operation-table size.  Everything else about
compatibility is *derived*, not checked.

```agda
  -- One root-replacement translate step per symbol, coordinate, and tuple.
  EdgeCompat : ParentVec card → Type
  EdgeCompat pv =
    ∀ (fi : Fin opCard) (c : Fin (arOf fi)) (t : Vec (Fin card) (arOf fi))
    → SameBlock pv (appIdx fi t) (appIdx fi (t [ c ]≔ parent pv (lookup t c)))

  edgeCompat? : (pv : ParentVec card) → Dec (EdgeCompat pv)
  edgeCompat? pv =
    all? (λ fi → all? (λ c → allVecsΠ? (λ t →
      parent pv (appIdx fi t) ≟ᶠ
        parent pv (appIdx fi (t [ c ]≔ parent pv (lookup t c))))))
```

The generalization from root-replacement steps to an arbitrary same-block
replacement at one coordinate: detour through the root of each side.

```agda
  -- Replacing one coordinate by a same-block index stays in the same block.
  stepSameBlock : (pv : ParentVec card) → EdgeCompat pv
    →  (fi : Fin opCard) (c : Fin (arOf fi)) (t : Vec (Fin card) (arOf fi))
    →  {a b : Fin card} → SameBlock pv a b
    →  SameBlock pv (appIdx fi (t [ c ]≔ a)) (appIdx fi (t [ c ]≔ b))
  stepSameBlock pv ec fi c t {a} {b} sab =
    trans (toRoot a) (trans mid (sym (toRoot b)))
    where
    -- the EdgeCompat step at entry z, rewritten to a one-shot update
    toRoot : (z : Fin card)
      → SameBlock pv (appIdx fi (t [ c ]≔ z)) (appIdx fi (t [ c ]≔ parent pv z))
    toRoot z = subst
      (λ v → SameBlock pv (appIdx fi (t [ c ]≔ z)) (appIdx fi v))
      (trans (cong (λ w → (t [ c ]≔ z) [ c ]≔ parent pv w) (lookup∘update c t z))
             ([]≔-idempotent t c))
      (ec fi c (t [ c ]≔ z))

    -- the two roots agree, so the two root-updated tuples agree
    mid : SameBlock pv (appIdx fi (t [ c ]≔ parent pv a))
                       (appIdx fi (t [ c ]≔ parent pv b))
    mid = cong (λ z → parent pv (appIdx fi (t [ c ]≔ z))) sab
```

Walking the coordinates.  `overwrite`{.AgdaFunction} replaces the entries of
`t` at a list of coordinates by those of the target `s`;
`overwrite-chain`{.AgdaFunction} shows each replacement preserves the claimed
block of the application (given blockwise-related tuples), and
`overwrite-stable`{.AgdaFunction} / `overwrite-∈`{.AgdaFunction} show a
coordinate once replaced stays replaced, so overwriting *all* coordinates
reaches `s` pointwise.

```agda
  -- Overwrite the entries of t at the listed coordinates with those of s.
  overwrite : {k : ℕ}
    → Vec (Fin card) k → List (Fin k) → Vec (Fin card) k → Vec (Fin card) k
  overwrite t []        s = t
  overwrite t (c ∷ cs)  s = overwrite (t [ c ]≔ lookup s c) cs s

  -- Componentwise same-block relatedness of two index tuples.
  Blockwise : (pv : ParentVec card) {k : ℕ}
    → Vec (Fin card) k → Vec (Fin card) k → Type
  Blockwise pv t s = ∀ q → SameBlock pv (lookup t q) (lookup s q)

  -- Each replacement step preserves the claimed block of the application.
  overwrite-chain : (pv : ParentVec card) → EdgeCompat pv
    →  (fi : Fin opCard) (cs : List (Fin (arOf fi)))
       (t s : Vec (Fin card) (arOf fi))
    →  Blockwise pv t s
    →  SameBlock pv (appIdx fi t) (appIdx fi (overwrite t cs s))
  overwrite-chain pv ec fi []        t s bw = refl
  overwrite-chain pv ec fi (c ∷ cs)  t s bw =
    trans (trans self (stepSameBlock pv ec fi c t (bw c)))
          (overwrite-chain pv ec fi cs (t [ c ]≔ lookup s c) s bw′)
    where
    -- t is its own one-shot update at c
    self : SameBlock pv (appIdx fi t) (appIdx fi (t [ c ]≔ lookup t c))
    self = cong (λ v → parent pv (appIdx fi v)) (sym ([]≔-lookup t c))

    -- the invariant survives the update
    bw′ : Blockwise pv (t [ c ]≔ lookup s c) s
    bw′ q with q ≟ᶠ c
    ... | yes q≡c =
      subst (λ z → SameBlock pv (lookup (t [ c ]≔ lookup s c) z) (lookup s z))
            (sym q≡c)
            (cong (parent pv) (lookup∘update c t (lookup s c)))
    ... | no q≢c =
      subst (λ w → SameBlock pv w (lookup s q))
            (sym (lookup∘update′ q≢c t (lookup s c)))
            (bw q)

  -- A coordinate that already agrees with s still agrees after overwriting.
  overwrite-stable : {k : ℕ} (t s : Vec (Fin card) k) (cs : List (Fin k))
    →  (q : Fin k) → lookup t q ≡ lookup s q
    →  lookup (overwrite t cs s) q ≡ lookup s q
  overwrite-stable t s []        q eq = eq
  overwrite-stable t s (c ∷ cs)  q eq with q ≟ᶠ c
  ... | yes q≡c =
    overwrite-stable _ s cs q
      (subst (λ z → lookup (t [ c ]≔ lookup s c) z ≡ lookup s z)
             (sym q≡c) (lookup∘update c t (lookup s c)))
  ... | no q≢c =
    overwrite-stable _ s cs q (trans (lookup∘update′ q≢c t (lookup s c)) eq)

  -- Overwriting at a listed coordinate lands that coordinate on s.
  overwrite-∈ : {k : ℕ} (t s : Vec (Fin card) k) (cs : List (Fin k)) (q : Fin k)
    →  q ∈ cs → lookup (overwrite t cs s) q ≡ lookup s q
  overwrite-∈ t s (c ∷ cs) q (here q≡c) =
    overwrite-stable _ s cs q
      (subst (λ z → lookup (t [ c ]≔ lookup s c) z ≡ lookup s z)
             (sym q≡c) (lookup∘update c t (lookup s c)))
  overwrite-∈ t s (c ∷ cs) q (there w) =
    overwrite-∈ _ s cs q w
```

Compatibility of the table relation.  For an enumerated symbol: encode the two
carrier tuples as index tuples, walk all coordinates with the chain lemma, and
close the gaps — between each carrier tuple and its encoding, and between the
fully overwritten tuple and the target encoding — by `≈`-congruence of the
interpretation plus `Coherent`{.AgdaFunction}.  An arbitrary symbol is an
enumerated one by surjectivity of the symbol enumeration, transported with an
explicit `subst`{.AgdaFunction} on a named motive (the same elaboration-hygiene
device as in [Setoid.Congruences.Presented.Decidable][]).

```agda
  -- The table relation is compatible with every enumerated operation symbol ...
  tableCompatAt : (pv : ParentVec card) → Coherent pv → EdgeCompat pv
    →  (fi : Fin opCard) {u v : ArityOf 𝑆 (opEnum fi) → 𝕌[ 𝑨 ]}
    →  (∀ a → TableRel pv (u a) (v a))
    →  TableRel pv ((opEnum fi ^ 𝑨) u) ((opEnum fi ^ 𝑨) v)
  tableCompatAt pv coh ec fi {u} {v} h =
    lift (trans (sym su) (trans chain (trans sbOw sv)))
    where
    f : OperationSymbolsOf 𝑆
    f = opEnum fi

    -- the index tuples encoding u and v
    tu tv : Vec (Fin card) (arOf fi)
    tu = tabulate (λ p → idx (u (arEnum f p)))
    tv = tabulate (λ p → idx (v (arEnum f p)))

    -- they are blockwise related, by the hypothesis
    bw : Blockwise pv tu tv
    bw p = subst₂ (SameBlock pv)
                  (sym (lookup∘tabulate (λ q → idx (u (arEnum f q))) p))
                  (sym (lookup∘tabulate (λ q → idx (v (arEnum f q))) p))
                  (lower (h (arEnum f p)))

    -- walking every coordinate turns tu into tv, blockwise
    chain : SameBlock pv (appIdx fi tu)
                         (appIdx fi (overwrite tu (allFin (arOf fi)) tv))
    chain = overwrite-chain pv ec fi (allFin (arOf fi)) tu tv bw

    -- the fully overwritten tuple is pointwise tv
    ow≡tv : ∀ q → lookup (overwrite tu (allFin (arOf fi)) tv) q ≡ lookup tv q
    ow≡tv q = overwrite-∈ tu tv (allFin (arOf fi)) q (∈-allFin q)

    sbOw : SameBlock pv (appIdx fi (overwrite tu (allFin (arOf fi)) tv))
                        (appIdx fi tv)
    sbOw = sameBlock-resp-≈ pv coh
      (Func.cong (Algebra.Interp 𝑨)
        (refl , λ a → ≈reflexive (cong enum (ow≡tv (arIdx f a)))))

    -- an encoded tuple is pointwise ≈ its original ...
    tu≈u : ∀ a → tupleOf fi tu a ≈ u a
    tu≈u a = ≈trans
      (≈reflexive (cong enum
        (trans (lookup∘tabulate (λ q → idx (u (arEnum f q))) (arIdx f a))
               (cong (λ b → idx (u b)) (arEnum-arIdx f a)))))
      (idx-≈ (u a))

    tv≈v : ∀ a → tupleOf fi tv a ≈ v a
    tv≈v a = ≈trans
      (≈reflexive (cong enum
        (trans (lookup∘tabulate (λ q → idx (v (arEnum f q))) (arIdx f a))
               (cong (λ b → idx (v b)) (arEnum-arIdx f a)))))
      (idx-≈ (v a))

    -- ... so its application is same-block with the original's
    su : SameBlock pv (appIdx fi tu) (idx ((f ^ 𝑨) u))
    su = sameBlock-resp-≈ pv coh (Func.cong (Algebra.Interp 𝑨) (refl , tu≈u))

    sv : SameBlock pv (appIdx fi tv) (idx ((f ^ 𝑨) v))
    sv = sameBlock-resp-≈ pv coh (Func.cong (Algebra.Interp 𝑨) (refl , tv≈v))

  -- ... hence with every operation symbol, by surjectivity of the enumeration.
  private
    TableCompatMotive : ParentVec card → OperationSymbolsOf 𝑆
      → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
    TableCompatMotive pv g = {u v : ArityOf 𝑆 g → 𝕌[ 𝑨 ]}
      →  (∀ a → TableRel pv (u a) (v a))
      →  TableRel pv ((g ^ 𝑨) u) ((g ^ 𝑨) v)

  tableCompat : (pv : ParentVec card) → Coherent pv → EdgeCompat pv
    →  𝑨 ∣≈ TableRel pv
  tableCompat pv coh ec f =
    subst (TableCompatMotive pv) (proj₂ (opEnum-sur f))
          (tableCompatAt pv coh ec (proj₁ (opEnum-sur f)))
```

The claimed partition is therefore a congruence — packaged with its
decision procedure as a `DecCon`{.AgdaFunction} whose decider is two lookups,
never a closure computation.

```agda
  -- The claimed partition as a congruence at the working level ...
  tableCon : (pv : ParentVec card) → Coherent pv → EdgeCompat pv
    →  Con 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  tableCon pv coh ec = TableRel pv , mkcon
    (tableReflexive pv coh)
    (record { refl   = lift refl
            ; sym    = λ e → lift (sym (lower e))
            ; trans  = λ e₁ e₂ → lift (trans (lower e₁) (lower e₂)) })
    (tableCompat pv coh ec)

  -- ... and as a decidable congruence.
  tableDecCon : (pv : ParentVec card) → Coherent pv → EdgeCompat pv
    →  DecCon 𝑨 (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  tableDecCon pv coh ec = tableCon pv coh ec , tableDec pv
```

#### C3, concluded: the generated congruence is contained in the claim

The seed pairs must land in the claimed blocks — the decidable
`Respects`{.AgdaFunction} sweep — and then `Cg-least`{.AgdaFunction} contains
the whole generated congruence in the table congruence.

```agda
  -- Every listed pair is same-block.
  Respects : ParentVec card → List IdxPair → Type
  Respects pv ps = All (λ p → SameBlock pv (proj₁ p) (proj₂ p)) ps

  respects? : (pv : ParentVec card) (ps : List IdxPair) → Dec (Respects pv ps)
  respects? pv ps = allL? (λ p → parent pv (proj₁ p) ≟ᶠ parent pv (proj₂ p)) ps

  -- Respected index pairs read back as table-related carrier pairs.
  private
    respected-carrier : (pv : ParentVec card) (ps : List IdxPair)
      →  Coherent pv → Respects pv ps
      →  All (λ q → TableRel pv (proj₁ q) (proj₂ q)) (carrierPairs ps)
    respected-carrier pv ps coh rsp = map⁺ (all-map step rsp)
      where
      step : {p : IdxPair} → SameBlock pv (proj₁ p) (proj₂ p)
        →   TableRel pv (enum (proj₁ p)) (enum (proj₂ p))
      step {p} sb = lift
        (trans (coh (idx (enum (proj₁ p))) (proj₁ p) (idx-≈ (enum (proj₁ p))))
               (trans sb (sym (coh (idx (enum (proj₂ p))) (proj₂ p) (idx-≈ (enum (proj₂ p)))))))

  -- The presented relation of a respected seed list is contained in the claim.
  fromPairs-table-⊆ : (pv : ParentVec card) (ps : List IdxPair)
    →  Coherent pv → Respects pv ps
    →  ∀ {x y} → fromPairs {𝑨 = 𝑨} (carrierPairs ps) x y → TableRel pv x y
  fromPairs-table-⊆ pv ps coh rsp mem =
    let (tab , x≈a , y≈b) = lookupAny (respected-carrier pv ps coh rsp) mem
    in  tableResp-≈ pv coh x≈a y≈b tab

  -- C3: the generated congruence of a respected seed list is contained in
  -- the claimed congruence (by the congruence generation theorem).
  Cg⊑table : (pv : ParentVec card) (ps : List IdxPair)
    →  (coh : Coherent pv) (ec : EdgeCompat pv) → Respects pv ps
    →  ∀ {x y} → Gen {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs ps)) x y
    →  TableRel pv x y
  Cg⊑table pv ps coh ec rsp =
    Cg-least (tableCon pv coh ec) (fromPairs-table-⊆ pv ps coh rsp)
```

The forest edges of an idempotent vector are respected by that vector itself —
each edge relates an index to its own root — so for the seed list
`forestEdges pv` the `Respects`{.AgdaFunction} obligation is free.

```agda
  -- A vector respects its own forest edges.
  edgesRespected : (pv : ParentVec card) → IdempotentParent pv
    →  Respects pv (forestEdges pv)
  edgesRespected pv idem =
    map⁺ (universal (λ i → sym (idem i))
                    (filter (λ i → ¬? (i ≟ᶠ parent pv i)) (allFin card)))
```

#### C1: trace soundness

Fix a seed list `ps`.  `GenPair ps`{.AgdaFunction} is membership of an index
pair in the generated congruence; `JustOK`{.AgdaFunction} is the validity of
one justification against the seed list and the already-processed merges
(most-recent-first, per the schema's reference conventions), stated through
`AtPos`{.AgdaFunction} so that decidability and consumption are both structural.

```agda
  -- Membership of an index pair in the congruence generated by the seeds.
  GenPair : List IdxPair → IdxPair → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  GenPair ps p =
    Gen {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs ps))
        (enum (proj₁ p)) (enum (proj₂ p))

  -- Validity of one justification for merging (i , j).
  JustOK : (ps done : List IdxPair) (i j : Fin card)
    →  Justification card opCard arOf → Type ρ
  JustOK ps done i j (seed s) =
    AtPos (λ p → (enum i ≈ enum (proj₁ p)) × (enum j ≈ enum (proj₂ p))) ps s
  JustOK ps done i j (translate fi c w r) =
    AtPos (λ p → (enum i ≈ (opEnum fi ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₁ p)))
               × (enum j ≈ (opEnum fi ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₂ p))))
          done r

  justOK? : (ps done : List IdxPair) (i j : Fin card)
    →  (ju : Justification card opCard arOf) → Dec (JustOK ps done i j ju)
  justOK? ps done i j (seed s) =
    atPos? (λ p → (enum i ≟ enum (proj₁ p)) ×-dec (enum j ≟ enum (proj₂ p))) ps s
  justOK? ps done i j (translate fi c w r) =
    atPos? (λ p → (enum i ≟ (opEnum fi ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₁ p)))
             ×-dec (enum j ≟ (opEnum fi ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₂ p))))
           done r
```

A valid trace is a run of valid justifications, each against the merges before
it; `merges`{.AgdaFunction} is the final accumulator.  Both are single
structural folds, as is the decider.

```agda
  -- Validity of a trace, processing merges into the accumulator done.
  TraceValidFrom : (ps done : List IdxPair)
    →  Trace card opCard arOf → Type ρ
  TraceValidFrom ps done [] = Lift ρ ⊤
  TraceValidFrom ps done (mkMerge i j ju ∷ tr) =
    JustOK ps done i j ju × TraceValidFrom ps ((i , j) ∷ done) tr

  traceValidFrom? : (ps done : List IdxPair) (tr : Trace card opCard arOf)
    →  Dec (TraceValidFrom ps done tr)
  traceValidFrom? ps done [] = yes (lift tt)
  traceValidFrom? ps done (mkMerge i j ju ∷ tr) =
    justOK? ps done i j ju ×-dec traceValidFrom? ps ((i , j) ∷ done) tr

  TraceValid : List IdxPair → Trace card opCard arOf → Type ρ
  TraceValid ps tr = TraceValidFrom ps [] tr

  traceValid? : (ps : List IdxPair) (tr : Trace card opCard arOf)
    →  Dec (TraceValid ps tr)
  traceValid? ps tr = traceValidFrom? ps [] tr

  -- The merged pairs of a trace, most recent first.
  mergesFrom : List IdxPair → Trace card opCard arOf → List IdxPair
  mergesFrom done []                     = done
  mergesFrom done (mkMerge i j _ ∷ tr)  = mergesFrom ((i , j) ∷ done) tr

  merges : Trace card opCard arOf → List IdxPair
  merges = mergesFrom []
```

A valid seed justification is `Any`-membership of the pair in the presented
relation — recovered structurally, at the recorded position.

```agda
  -- A valid seed reference presents the merged pair.
  seedAt : (ps : List IdxPair) (s : ℕ) {i j : Fin card}
    →  AtPos (λ p → (enum i ≈ enum (proj₁ p)) × (enum j ≈ enum (proj₂ p))) ps s
    →  fromPairs {𝑨 = 𝑨} (carrierPairs ps) (enum i) (enum j)
  seedAt []        s        (lift ())
  seedAt (p ∷ ps)  zero     ok = here ok
  seedAt (p ∷ ps)  (suc s)  ok = there (seedAt ps s ok)
```

One valid justification yields one `Gen`{.AgdaDatatype} derivation: a seed by
the `base`{.AgdaInductiveConstructor} rule; a translate by one
`compatible`{.AgdaInductiveConstructor} rule applied to the earlier merge at
the moving coordinate and to reflexivity at the frozen coordinates, wrapped in
the recorded `≈`-matches.  This is obligation C1, entry by entry.

```agda
  -- C1, one entry: a valid justification derives its merged pair.
  justGen : (ps done : List IdxPair) {i j : Fin card}
    →  (ju : Justification card opCard arOf)
    →  All (GenPair ps) done → JustOK ps done i j ju → GenPair ps (i , j)
  justGen ps done (seed s) dall ok = base (seedAt ps s ok)
  justGen ps done {i} {j} (translate fi c w r) dall ok =
    atPos-use done r dall ok derive
    where
    f : OperationSymbolsOf 𝑆
    f = opEnum fi

    derive : (p : IdxPair) → GenPair ps p
      →  (enum i ≈ (f ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₁ p)))
       × (enum j ≈ (f ^ 𝑨) (tupleOf fi (w [ c ]≔ proj₂ p)))
      →  GenPair ps (i , j)
    derive (x , y) gxy (ei≈ , ej≈) =
      transitive (rfl ei≈)
        (transitive (compatible f ptw) (symmetric (rfl ej≈)))
      where
      R : BinaryRel 𝕌[ 𝑨 ] (α ⊔ ρ)
      R = fromPairs {𝑨 = 𝑨} (carrierPairs ps)

      -- the two frozen tuples are pointwise generated-related:
      -- the moving coordinate by the earlier merge, the rest by reflexivity
      ptw : ∀ a → Gen {𝑨 = 𝑨} R (tupleOf fi (w [ c ]≔ x) a)
                                (tupleOf fi (w [ c ]≔ y) a)
      ptw a with arIdx f a ≟ᶠ c
      ... | yes p =
        subst₂ (λ s′ t′ → Gen {𝑨 = 𝑨} R (enum s′) (enum t′))
               (sym (trans (cong (lookup (w [ c ]≔ x)) p) (lookup∘update c w x)))
               (sym (trans (cong (lookup (w [ c ]≔ y)) p) (lookup∘update c w y)))
               gxy
      ... | no ¬p =
        subst₂ (λ s′ t′ → Gen {𝑨 = 𝑨} R (enum s′) (enum t′))
               (sym (lookup∘update′ ¬p w x))
               (sym (lookup∘update′ ¬p w y))
               (rfl ≈refl)
```

C1, the whole trace: fold the entries, accumulating each derived pair.

```agda
  -- C1: every merged pair of a valid trace is generated.
  traceGenFrom : (ps done : List IdxPair) (tr : Trace card opCard arOf)
    →  All (GenPair ps) done → TraceValidFrom ps done tr
    →  All (GenPair ps) (mergesFrom done tr)
  traceGenFrom ps done [] dall _ = dall
  traceGenFrom ps done (mkMerge i j ju ∷ tr) dall (ok , rest) =
    traceGenFrom ps ((i , j) ∷ done) tr (justGen ps done ju dall ok ∷ dall) rest

  traceGen : (ps : List IdxPair) (tr : Trace card opCard arOf)
    →  TraceValid ps tr → All (GenPair ps) (merges tr)
  traceGen ps tr tv = traceGenFrom ps [] tr [] tv
```

#### C2: replaying the merges

The replay state is a root vector, initially the identity.  Processing one
merged pair re-points every index rooted at the right root to the left root —
the eager, proofless core of a union-find, adequate because the checker replays
a *given* ≤ `n − 1`-entry list exactly once.  (`merges`{.AgdaFunction} is
most-recent-first, and `foldr`{.AgdaFunction} therefore applies the *head*
last: the replay processes the trace in run order.)

```agda
  -- Re-point one root: entries rooted at rv move to ru.
  repoint : Fin card → Fin card → Fin card → Fin card
  repoint ru rv r = if does (r ≟ᶠ rv) then ru else r

  -- Process one merged pair.
  replayStep : Vec (Fin card) card → IdxPair → Vec (Fin card) card
  replayStep st p =
    mapᵥ (repoint (lookup st (proj₁ p)) (lookup st (proj₂ p))) st

  -- Replay a merge list from the identity partition.
  replayRoots : List IdxPair → Vec (Fin card) card
  replayRoots ms = foldr (λ p st → replayStep st p) (tabulate (λ i → i)) ms
```

The soundness invariant: every index is generated-related to its current
replay root.  It holds initially by reflexivity and is preserved by each step —
the re-pointed indices reach their new root through the merged pair.

```agda
  -- Every index is generated-related to its replay root.
  ReplaySound : List IdxPair → Vec (Fin card) card → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ)
  ReplaySound ps st = ∀ i → GenPair ps (i , lookup st i)

  private
    -- one re-pointed entry, with the decision exposed as an argument
    repoint-gen : (ps : List IdxPair) {ru rv : Fin card} (r : Fin card)
      →  (d : Dec (r ≡ rv)) {i : Fin card}
      →  GenPair ps (i , r) → GenPair ps (rv , ru)
      →  GenPair ps (i , (if does d then ru else r))
    repoint-gen ps r (yes q) g h =
      transitive g (subst (λ z → GenPair ps (z , _)) (sym q) h)
    repoint-gen ps r (no _)  g _ = g

  -- One step preserves the invariant.
  replayStep-sound : (ps : List IdxPair) (st : Vec (Fin card) card)
    →  (p : IdxPair) → GenPair ps p → ReplaySound ps st
    →  ReplaySound ps (replayStep st p)
  replayStep-sound ps st (u , v) guv snd i =
    subst (λ z → GenPair ps (i , z))
          (sym (lookup-map i (repoint (lookup st u) (lookup st v)) st))
          (repoint-gen ps (lookup st i) (lookup st i ≟ᶠ lookup st v)
                       (snd i) rv→ru)
    where
    -- from the old right root to the old left root, through the merged pair
    rv→ru : GenPair ps (lookup st v , lookup st u)
    rv→ru = transitive (symmetric (snd v))
                       (transitive (symmetric guv) (snd u))

  -- The invariant holds after replaying a generated merge list.
  replay-sound : (ps ms : List IdxPair)
    →  All (GenPair ps) ms → ReplaySound ps (replayRoots ms)
  replay-sound ps [] [] i =
    subst (λ z → GenPair ps (i , z))
          (sym (lookup∘tabulate (λ j → j) i)) (rfl ≈refl)
  replay-sound ps (p ∷ ms) (g ∷ gs) =
    replayStep-sound ps (replayRoots ms) p g (replay-sound ps ms gs)
```

The alignment condition `Covers`{.AgdaFunction}: the replayed roots are
constant along the claimed parent pointers.  One linear sweep, and exactly what
the containment argument consumes — if two indices share a claimed parent, they
share a replayed root, hence both are generated-related to it.  (No converse
sweep is needed: the *other* inclusion is C3, and an over-merging trace would
merely make the two checks jointly unsatisfiable, never unsound.)

```agda
  -- The replayed roots are constant along the claimed parent pointers.
  Covers : ParentVec card → Vec (Fin card) card → Type
  Covers pv rr = ∀ i → lookup rr (parent pv i) ≡ lookup rr i

  covers? : (pv : ParentVec card) (rr : Vec (Fin card) card)
    →  Dec (Covers pv rr)
  covers? pv rr = all? (λ i → lookup rr (parent pv i) ≟ᶠ lookup rr i)

  -- C2: the claimed congruence is contained in the generated one.
  table⊑Cg : (pv : ParentVec card) (ps : List IdxPair)
    →  (tr : Trace card opCard arOf)
    →  TraceValid ps tr → Covers pv (replayRoots (merges tr))
    →  ∀ {x y} → TableRel pv x y
    →  Gen {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs ps)) x y
  table⊑Cg pv ps tr tv cov {x} {y} (lift same) =
    transitive (symmetric (rfl (idx-≈ x)))
      (transitive (snd (idx x))
        (transitive (rfl (≈reflexive (cong enum key)))
          (transitive (symmetric (snd (idx y))) (rfl (idx-≈ y)))))
    where
    rr : Vec (Fin card) card
    rr = replayRoots (merges tr)

    snd : ReplaySound ps (replayRoots (merges tr))
    snd = replay-sound ps (merges tr) (traceGen ps tr tv)

    -- same claimed parent forces same replayed root
    key : lookup rr (idx x) ≡ lookup rr (idx y)
    key = trans (sym (cov (idx x)))
                (trans (cong (lookup rr) same) (cov (idx y)))
```

#### The trace-free special case: a vector generates itself from its edges

When the seed list is the vector's *own* forest edges, no trace is needed: an
index reaches its root in one edge (or is a root), so the containment of the
claim in the generated congruence is direct.  This is the form the
whole-lattice checker uses for every listed congruence.

```agda
  -- Every index is edge-generated-related to its root.
  toRootGen : (pv : ParentVec card) (i : Fin card)
    →  Gen {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs (forestEdges pv)))
           (enum i) (enum (parent pv i))
  toRootGen pv i with i ≟ᶠ parent pv i
  ... | yes q = rfl (≈reflexive (cong enum q))
  ... | no ¬q = base (lose mem (≈refl , ≈refl))
    where
    mem : (enum i , enum (parent pv i)) ∈ carrierPairs (forestEdges pv)
    mem = ∈-map⁺ (λ p → enum (proj₁ p) , enum (proj₂ p))
            (∈-map⁺ (λ a → a , parent pv a)
              (∈-filter⁺ (λ a → ¬? (a ≟ᶠ parent pv a)) (∈-allFin i) ¬q))

  -- The claimed congruence is contained in the one its edges generate.
  table⊑CgEdges : (pv : ParentVec card)
    →  ∀ {x y} → TableRel pv x y
    →  Gen {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs (forestEdges pv))) x y
  table⊑CgEdges pv {x} {y} (lift same) =
    transitive (symmetric (rfl (idx-≈ x)))
      (transitive (toRootGen pv (idx x))
        (transitive (rfl (≈reflexive (cong enum same)))
          (transitive (symmetric (toRootGen pv (idx y))) (rfl (idx-≈ y)))))
```

#### The headline theorems

Both directions, packaged as an honest `_≑_`{.AgdaFunction} at the working
congruence level: with a trace, for an arbitrary seed list; and trace-free,
for a vector against its own forest edges.

```agda
  -- θ ≑ Cg (fromPairs P), from a checked certificate.
  table≑Cg : (pv : ParentVec card) (ps : List IdxPair)
    →  (tr : Trace card opCard arOf)
    →  (coh : Coherent pv) (ec : EdgeCompat pv)
    →  Respects pv ps → TraceValid ps tr
    →  Covers pv (replayRoots (merges tr))
    →  tableCon pv coh ec ≑ Cg {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs ps))
  table≑Cg pv ps tr coh ec rsp tv cov =
    table⊑Cg pv ps tr tv cov , Cg⊑table pv ps coh ec rsp

  -- θ ≑ Cg (its own forest edges), with no trace at all.
  table≑CgEdges : (pv : ParentVec card)
    →  (coh : Coherent pv) (ec : EdgeCompat pv) → IdempotentParent pv
    →  tableCon pv coh ec
         ≑ Cg {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs (forestEdges pv)))
  table≑CgEdges pv coh ec idem =
    table⊑CgEdges pv , Cg⊑table pv (forestEdges pv) coh ec (edgesRespected pv idem)
```

Finally, the bundled interface for one standalone certificate: the conjunction
of all five checked conditions, its decider (one decision for the whole
certificate), and the soundness theorem consuming it.

```agda
  -- All checked conditions of one per-congruence certificate.
  CgCertOK : CgCert card opCard arOf → Type ρ
  CgCertOK cc =
    Coherent part × EdgeCompat part × Respects part seeds
      × TraceValid seeds trace × Covers part (replayRoots (merges trace))
    where open CgCert cc

  cgCertOK? : (cc : CgCert card opCard arOf) → Dec (CgCertOK cc)
  cgCertOK? cc =
    coherent? part ×-dec edgeCompat? part ×-dec respects? part seeds
      ×-dec traceValid? seeds trace ×-dec covers? part (replayRoots (merges trace))
    where open CgCert cc

  -- The certificate's claim, from its checked conditions.
  cgCertSound : (cc : CgCert card opCard arOf) (ok : CgCertOK cc)
    →  tableCon (CgCert.part cc) (proj₁ ok) (proj₁ (proj₂ ok))
         ≑ Cg {𝑨 = 𝑨} (fromPairs {𝑨 = 𝑨} (carrierPairs (CgCert.seeds cc)))
  cgCertSound cc (coh , ec , rsp , tv , cov) =
    table≑Cg (CgCert.part cc) (CgCert.seeds cc) (CgCert.trace cc)
             coh ec rsp tv cov
```

--------------------------------------

[^1]: [PR #467](https://github.com/ualib/agda-algebras/pull/467)
