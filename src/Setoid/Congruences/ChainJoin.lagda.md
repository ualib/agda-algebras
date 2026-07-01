---
layout: default
file: "src/Setoid/Congruences/ChainJoin.lagda.md"
title: "Setoid.Congruences.ChainJoin module"
date: "2026-06-28"
author: "the agda-algebras development team"
---

### Finite alternating chains and the join of two congruences

This is the [Setoid.Congruences.ChainJoin][] module of the [Agda Universal Algebra Library][].

[Setoid.Congruences.Generation][] builds the join `θ ∨ φ = Cg(θ ∪ φ)` as the
*inductively generated* congruence `Gen(θ ∪ φ)`, whose `compatible` constructor closes the
relation under the basic operations.  That closure is needed for **infinitary**
signatures.  For a **finitary** signature — every operation symbol has a finite arity,
the universal-algebraist's standing assumption — the join collapses to something far more
concrete: the **finite alternating chain** `x ≈ · (θ∪φ) · (θ∪φ) ⋯ · ≈ y`.

This module makes that precise.  It defines the chain relation `Chain 𝑩 R`, shows a chain
is always below the generated congruence (`Chain⊆Gen`), and — the substantive content —
shows that for a finitary signature the chain relation is itself a *congruence*, so by the
least-upper-bound property `Cg-least` the generated join is *contained in* it
(`finitary⇒JoinIsChain`).  The two inclusions together identify the join with the chain
relation for finitary algebras.

The downstream client is the forward direction of Jónsson's theorem
([Setoid.Varieties.Maltsev.Distributivity][]), whose staircase is proved against `Chain` in
full generality; `finitary⇒JoinIsChain` is what upgrades it from the chain statement to
the literal `CongruenceDistributive` for the finitary algebras of ordinary universal
algebra.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Congruences.ChainJoin where

-- Imports from Agda and the Agda Standard Library ----------------------------
open import Agda.Primitive                  using () renaming ( Set to Type )
open import Data.Bool.Base                  using ( Bool ; true ; false ; T ; if_then_else_ )
open import Data.Empty                      using ( ⊥-elim )
open import Data.Fin.Base                   using ( Fin ; toℕ ; fromℕ< )
open import Data.Fin.Properties             using ( _≟_ ; toℕ<n ; toℕ-fromℕ< ; toℕ-injective )
open import Data.Nat.Base                   using ( ℕ ; zero ; suc ; _<_ ; _<ᵇ_ ; _≤_ )
open import Data.Nat.Properties             using ( <⇒<ᵇ ; ≤-refl ; ≤-trans ; n<1+n ; n≤1+n )
open import Data.Product                    using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                   using ( inj₁ ; inj₂ ; [_,_] )
open import Function.Base                   using ( _∘_ ; const )
open import Function.Bundles                using ( _↔_ ; Inverse )
open import Level                           using ( Level ; _⊔_ ) renaming ( suc to lsuc)
open import Relation.Nullary.Decidable      using ( yes ; no )
open import Relation.Binary                 using ( Setoid ; IsEquivalence )

open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Overture                       using  ( OperationSymbolsOf ; ArityOf )
open import Setoid.Algebras.Basic          using  ( Algebra ; 𝔻[_] ; 𝕌[_] ; _^_ )
open import Setoid.Congruences.Basic       using  ( Con ; mkcon ; _∣≈_ ; reflexive
                                                  ; is-equivalence ; is-compatible )
open import Setoid.Congruences.Generation  using  ( Gen ; rfl ; transitive ; base
                                                  ; Cg-least ; _∪ᵣ_ )

open import Function using ( Func )
open Func renaming ( cong to ≈cong ; to to _⟨$⟩_ )
open Algebra using ( Interp )

private variable α ρ ℓ : Level
```

#### The alternating-chain relation

A `Chain 𝑩 R` from `x` to `y` is a finite walk `x ≈ · R · R ⋯ R · ≈ y`: the
reflexive–transitive closure of a relation `R` on the carrier of `𝑩`.  We use it with
`R = θ ∪ᵣ φ`, so each `cons` step is tagged (by the `⊎` of `_∪ᵣ_`) as a θ-step or a φ-step.
The carrier algebra `𝑩` is an *explicit* parameter, since it cannot be inferred from a
relation on `𝕌[ 𝑩 ]` (the carrier projection is not injective).

```agda
data Chain {𝑆 : Signature 𝓞 𝓥} (𝑩 : Algebra {𝑆 = 𝑆} α ρ)(R : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type ℓ)
  : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type (α ⊔ ρ ⊔ ℓ) where
  nil  : {x y : 𝕌[ 𝑩 ]} → Setoid._≈_ 𝔻[ 𝑩 ] x y → Chain 𝑩 R x y
  cons : {x y z : 𝕌[ 𝑩 ]} → R x y → Chain 𝑩 R y z → Chain 𝑩 R x z
```

The closure laws.  A trailing setoid-equality step is absorbed unconditionally; a *leading*
one (`chain-≈ˡ`) needs `R` to respect `≈` on the left, and symmetry needs `R` symmetric —
both supplied for `θ ∪ᵣ φ` from the two congruences (`R-resp` / `R-sym` below).  We keep the
inductions generic in those two facts.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑩 : Algebra {𝑆 = 𝑆} α ρ} {R : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type ℓ} where
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )

  -- A chain absorbs a trailing setoid-equality step.
  chain-≈ʳ : {x y z : 𝕌[ 𝑩 ]} → Chain 𝑩 R x y → y ≈ z → Chain 𝑩 R x z
  chain-≈ʳ (nil x≈y)  y≈z = nil (≈trans x≈y y≈z)
  chain-≈ʳ (cons r c) y≈z = cons r (chain-≈ʳ c y≈z)

  -- A chain absorbs a leading setoid-equality step (R respects ≈ on the left).
  chain-≈ˡ : ({a b c : 𝕌[ 𝑩 ]} → a ≈ b → R b c → R a c)
    → {x y z : 𝕌[ 𝑩 ]} → x ≈ y → Chain 𝑩 R y z → Chain 𝑩 R x z
  chain-≈ˡ Rresp x≈y (nil y≈z)  = nil (≈trans x≈y y≈z)
  chain-≈ˡ Rresp x≈y (cons r c) = cons (Rresp x≈y r) c

  -- Transitivity (concatenation).
  chain-trans : ({a b c : 𝕌[ 𝑩 ]} → a ≈ b → R b c → R a c)
    → {x y z : 𝕌[ 𝑩 ]} → Chain 𝑩 R x y → Chain 𝑩 R y z → Chain 𝑩 R x z
  chain-trans Rresp (nil x≈y)  d = chain-≈ˡ Rresp x≈y d
  chain-trans Rresp (cons r c) d = cons r (chain-trans Rresp c d)

  -- Symmetry, given R symmetric and ≈-respecting.
  chain-sym : ({a b c : 𝕌[ 𝑩 ]} → a ≈ b → R b c → R a c) → ({a b : 𝕌[ 𝑩 ]} → R a b → R b a)
    → {x y : 𝕌[ 𝑩 ]} → Chain 𝑩 R x y → Chain 𝑩 R y x
  chain-sym Rresp Rsym (nil x≈y)  = nil (≈sym x≈y)
  chain-sym Rresp Rsym (cons r c) =
    chain-trans Rresp (chain-sym Rresp Rsym c) (cons (Rsym r) (nil ≈refl))
```

#### A chain is below the generated congruence

Each step is `base`, the empty walk is `rfl`, concatenation is `transitive`.

```agda
Chain⊆Gen : {𝑆 : Signature 𝓞 𝓥} (𝑩 : Algebra {𝑆 = 𝑆} α ρ) (θ φ : Con 𝑩 ℓ) {x y : 𝕌[ 𝑩 ]}
  → Chain 𝑩 (θ ∪ᵣ φ) x y → Gen {𝑨 = 𝑩} (θ ∪ᵣ φ) x y
Chain⊆Gen 𝑩 θ φ (nil x≈y)   = rfl x≈y
Chain⊆Gen 𝑩 θ φ (cons r c)  = transitive (base r) (Chain⊆Gen 𝑩 θ φ c)
```

#### Finitary signatures

A signature is **finitary** when every operation symbol has a finite arity — a finite
bijection `ArityOf 𝑆 f ↔ Fin k`.  This is the standing assumption of ordinary (finitary)
universal algebra, and for the signatures of the library it is *immediate*: each arity is a
concrete `Fin k`, so the witness is the identity bijection `↔-id` at every symbol —
`λ _ → _ , ↔-id`.

```agda
Finitary : (𝑆 : Signature 𝓞 𝓥) → Type (𝓞 ⊔ 𝓥)
Finitary 𝑆 = (f : OperationSymbolsOf 𝑆) → Σ[ k ∈ ℕ ] (ArityOf 𝑆 f ↔ Fin k)
```

#### Operations preserve the chain relation, one coordinate at a time

This is the substantive lemma.  An operation `op` of arity `Fin k` that respects the
setoid equality and both congruences `θ`, `φ` also respects the chain relation `θ ∪ᵣ φ`:
pointwise-chained inputs give chained outputs.  The proof changes the `k` coordinates of
`op`'s argument from `g` to `g′` *one at a time* (`shift1`), folding the per-coordinate
chains into a single walk; finiteness of the arity is exactly what makes the fold
terminate.

Two `Bool`/`<ᵇ` facts drive the fold.

```agda
private
  T⇒true : {b : Bool} → T b → b ≡ true
  T⇒true {true} _ = refl

  n<ᵇn≡false : (n : ℕ) → (n <ᵇ n) ≡ false
  n<ᵇn≡false zero    = refl
  n<ᵇn≡false (suc n) = n<ᵇn≡false n

  -- away from the boundary `m`, raising the bound by one is invisible
  <ᵇ-step-≠ : (a m : ℕ) → a ≢ m → (a <ᵇ m) ≡ (a <ᵇ suc m)
  <ᵇ-step-≠ zero    zero    a≢m = ⊥-elim (a≢m refl)
  <ᵇ-step-≠ zero    (suc m) _   = refl
  <ᵇ-step-≠ (suc a) zero    _   = refl
  <ᵇ-step-≠ (suc a) (suc m) a≢m = <ᵇ-step-≠ a m (λ a≡m → a≢m (cong suc a≡m))

module _
  {𝑆 : Signature 𝓞 𝓥}
  {𝑩 : Algebra {𝑆 = 𝑆} α ρ}(θ φ : Con 𝑩 ℓ) where
  open Setoid 𝔻[ 𝑩 ] using ( _≈_ )
    renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans ; reflexive to ≡→≈ )
  private
    θc = proj₂ θ
    φc = proj₂ φ
    R : 𝕌[ 𝑩 ] → 𝕌[ 𝑩 ] → Type ℓ
    R = θ ∪ᵣ φ

  -- For two congruences, their union respects ≈ on the left and is symmetric.
  R-resp : {a b c : 𝕌[ 𝑩 ]} → a ≈ b → R b c → R a c
  R-resp a≈b (inj₁ θbc) = inj₁ (IsEquivalence.trans (is-equivalence θc) (reflexive θc a≈b) θbc)
  R-resp a≈b (inj₂ φbc) = inj₂ (IsEquivalence.trans (is-equivalence φc) (reflexive φc a≈b) φbc)

  R-sym : {a b : 𝕌[ 𝑩 ]} → R a b → R b a
  R-sym (inj₁ θab) = inj₁ (IsEquivalence.sym (is-equivalence θc) θab)
  R-sym (inj₂ φab) = inj₂ (IsEquivalence.sym (is-equivalence φc) φab)

  -- Fix a `k`-ary operation `op`, compatible with ≈ and with both congruences.
  module _ (k : ℕ)(op : (Fin k → 𝕌[ 𝑩 ]) → 𝕌[ 𝑩 ])
    (op≈ : (a b : Fin k → 𝕌[ 𝑩 ]) → (∀ i → a i ≈ b i) → op a ≈ op b)
    (opCong : (μ : Con 𝑩 ℓ)(a b : Fin k → 𝕌[ 𝑩 ])
              → (∀ i → proj₁ μ (a i) (b i)) → proj₁ μ (op a) (op b))
    where

    -- Change one coordinate `i` of `op`'s argument along a chain.  The chain's *start*
    -- index `z` is kept `≈`-flexible (not pinned to `w i`) so the recursion is structural
    -- in the chain, which the termination checker needs through the `updateAt` rewrites.
    shift1 : (i : Fin k)(w : Fin k → 𝕌[ 𝑩 ])(z c : 𝕌[ 𝑩 ]) → w i ≈ z → Chain 𝑩 R z c
      → Chain 𝑩 R (op w) (op (updateAt w i (const c)))
    shift1 i w z c wi≈z (nil z≈c) = nil (op≈ w (updateAt w i (const c)) ptwise)
      where
      ptwise : (j : Fin k) → w j ≈ updateAt w i (const c) j
      ptwise j with i ≟ j
      ... | yes refl = ≈trans (≈trans wi≈z z≈c) (≈sym (≡→≈ (updateAt-updates i w)))
      ... | no  i≢j  = subst (w j ≈_) (sym (updateAt-minimal j i w (i≢j ∘ sym))) ≈refl
    shift1 i w z c wi≈z (cons {y = y} s rest) =
      cons step (chain-≈ʳ (shift1 i (updateAt w i (const y)) y c (≡→≈ (updateAt-updates i w)) rest) endpt)
      where
      ptwiseμ : (μ : Con 𝑩 ℓ) → proj₁ μ (w i) y
        → (j : Fin k) → proj₁ μ (w j) (updateAt w i (const y) j)
      ptwiseμ μ μwiy j with i ≟ j
      ... | yes refl = subst (proj₁ μ (w i)) (sym (updateAt-updates i w)) μwiy
      ... | no  i≢j  = subst (proj₁ μ (w j)) (sym (updateAt-minimal j i w (i≢j ∘ sym)))
                             (reflexive (proj₂ μ) ≈refl)
      step : R (op w) (op (updateAt w i (const y)))
      step = [ (λ θwiy → inj₁ (opCong θ w (updateAt w i (const y)) (ptwiseμ θ θwiy)))
             , (λ φwiy → inj₂ (opCong φ w (updateAt w i (const y)) (ptwiseμ φ φwiy))) ]
             (R-resp wi≈z s)
      endpt : op (updateAt (updateAt w i (const y)) i (const c)) ≈ op (updateAt w i (const c))
      endpt = op≈ _ _ (λ j → ≡→≈ (updateAt-updateAt i w j))

    -- The fold: changing all `k` coordinates of `op`'s argument from `g` to `g′`.  The
    -- hybrid `mix m` keeps coordinates with index `< m` at `g′` and the rest at `g`, so
    -- `mix 0 = g`, `mix k = g′`, and `mix m → mix (suc m)` is a single-coordinate move.
    chain-op : (g g′ : Fin k → 𝕌[ 𝑩 ]) → ((i : Fin k) → Chain 𝑩 R (g i) (g′ i))
      → Chain 𝑩 R (op g) (op g′)
    chain-op g g′ H = chain-≈ʳ (build k ≤-refl) (op≈ (mix k) g′ mixk)
      where
      mix : ℕ → Fin k → 𝕌[ 𝑩 ]
      mix m i = if (toℕ i <ᵇ m) then g′ i else g i

      mixk : (i : Fin k) → mix k i ≈ g′ i
      mixk i = ≡→≈ (cong (λ b → if b then g′ i else g i) (T⇒true (<⇒<ᵇ (toℕ<n i))))

      step : (m : ℕ)(m<k : m < k) → Chain 𝑩 R (op (mix m)) (op (mix (suc m)))
      step m m<k =
        chain-≈ʳ (shift1 iₘ (mix m) (g iₘ) (g′ iₘ) (≡→≈ mix-m-iₘ) (H iₘ)) endpt
        where
        iₘ : Fin k
        iₘ = fromℕ< m<k
        tiₘ : toℕ iₘ ≡ m
        tiₘ = toℕ-fromℕ< m<k
        mix-m-iₘ : mix m iₘ ≡ g iₘ
        mix-m-iₘ = cong (λ b → if b then g′ iₘ else g iₘ)
                        (trans (cong (_<ᵇ m) tiₘ) (n<ᵇn≡false m))
        endpt : op (updateAt (mix m) iₘ (const (g′ iₘ))) ≈ op (mix (suc m))
        endpt = op≈ _ _ ptwise
          where
          ptwise : (j : Fin k) → updateAt (mix m) iₘ (const (g′ iₘ)) j ≈ mix (suc m) j
          ptwise j with iₘ ≟ j
          ... | yes refl = ≡→≈ (trans (updateAt-updates iₘ (mix m)) (sym mix-suc-iₘ))
            where
            mix-suc-iₘ : mix (suc m) iₘ ≡ g′ iₘ
            mix-suc-iₘ = cong (λ b → if b then g′ iₘ else g iₘ)
                              (trans (cong (_<ᵇ suc m) tiₘ) (T⇒true (<⇒<ᵇ (n<1+n m))))
          ... | no iₘ≢j = ≡→≈ (trans (updateAt-minimal j iₘ (mix m) (iₘ≢j ∘ sym)) mix-agree)
            where
            tj≢m : toℕ j ≢ m
            tj≢m tj≡m = iₘ≢j (toℕ-injective (trans tiₘ (sym tj≡m)))
            mix-agree : mix m j ≡ mix (suc m) j
            mix-agree = cong (λ b → if b then g′ j else g j) (<ᵇ-step-≠ (toℕ j) m tj≢m)

      build : (m : ℕ) → m ≤ k → Chain 𝑩 R (op g) (op (mix m))
      build zero    _    = nil (op≈ g (mix 0) (λ _ → ≈refl))
      build (suc m) sm≤k = chain-trans R-resp (build m (≤-trans (n≤1+n m) sm≤k)) (step m sm≤k)
```

#### The chain relation is a congruence, and the join is a chain

Given a finitary signature, the chain relation `θ ∪ᵣ φ` is compatible with every basic
operation: present the operation as a `Fin k`-ary `op` through the arity bijection, hand its
`≈`- and congruence-compatibility (from `Interp` and `is-compatible`) to the fold `chain-op`,
and translate the result back across the bijection.

```agda
  chain-compatible : Finitary 𝑆 → 𝑩 ∣≈ Chain 𝑩 R
  chain-compatible fin f {u}{v} H = chain-≈ˡ R-resp (≈sym opu) (chain-≈ʳ folded opv)
    where
    k    = proj₁ (fin f)
    ev   = proj₂ (fin f)
    to   = Inverse.to ev
    from = Inverse.from ev
    op : (Fin k → 𝕌[ 𝑩 ]) → 𝕌[ 𝑩 ]
    op h = (f ^ 𝑩) (h ∘ to)
    op≈ : (a b : Fin k → 𝕌[ 𝑩 ]) → (∀ i → a i ≈ b i) → op a ≈ op b
    op≈ a b a≈b = ≈cong (Interp 𝑩) (refl , λ x → a≈b (to x))
    opCong : (μ : Con 𝑩 ℓ)(a b : Fin k → 𝕌[ 𝑩 ])
             → (∀ i → proj₁ μ (a i) (b i)) → proj₁ μ (op a) (op b)
    opCong μ a b ab = is-compatible (proj₂ μ) f (λ x → ab (to x))
    folded : Chain 𝑩 R (op (u ∘ from)) (op (v ∘ from))
    folded = chain-op k op op≈ opCong (u ∘ from) (v ∘ from) (λ j → H (from j))
    -- `op` precomposed with `from` recovers the original operation (round-trip on the arity)
    opu : op (u ∘ from) ≈ (f ^ 𝑩) u
    opu = ≈cong (Interp 𝑩) (refl , λ x → ≡→≈ (cong u (Inverse.strictlyInverseʳ ev x)))
    opv : op (v ∘ from) ≈ (f ^ 𝑩) v
    opv = ≈cong (Interp 𝑩) (refl , λ x → ≡→≈ (cong v (Inverse.strictlyInverseʳ ev x)))

  -- Hence, for a finitary signature, the chain relation is a congruence.
  Chain-Con : Finitary 𝑆 → Con 𝑩 (α ⊔ ρ ⊔ ℓ)
  Chain-Con fin = Chain 𝑩 R , mkcon nil chain-isEquiv (chain-compatible fin)
    where
    chain-isEquiv : IsEquivalence (Chain 𝑩 R)
    chain-isEquiv = record { refl  = nil ≈refl
                           ; sym   = chain-sym R-resp R-sym
                           ; trans = chain-trans R-resp }

  -- The least-upper-bound property then contains the generated join in the chain relation.
  finitary⇒Gen⊆Chain : Finitary 𝑆 → {x y : 𝕌[ 𝑩 ]} → Gen {𝑨 = 𝑩} R x y → Chain 𝑩 R x y
  finitary⇒Gen⊆Chain fin = Cg-least (Chain-Con fin) (λ r → cons r (nil ≈refl))
```

Packaging the two inclusions: for a finitary signature, membership in the generated join
`Cg(θ ∪ φ)` is *witnessed by a finite chain*.  This is exactly the `JoinIsChain` hypothesis
that the forward direction of Jónsson's theorem
([Setoid.Varieties.Maltsev.Distributivity][]) needs in order to land in the literal
`CongruenceDistributive`.

```agda
-- The generated join Cg(θ ∪ φ) is witnessed by finite alternating chains, for all θ, φ.
JoinIsChain : {𝑆 : Signature 𝓞 𝓥} (𝑨 : Algebra {𝑆 = 𝑆} α ρ)(ℓ : Level) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρ ⊔ lsuc ℓ)
JoinIsChain 𝑨 ℓ =
  (θ φ : Con 𝑨 ℓ){x y : 𝕌[ 𝑨 ]} → Gen {𝑨 = 𝑨} (θ ∪ᵣ φ) x y → Chain 𝑨 (θ ∪ᵣ φ) x y

finitary⇒JoinIsChain : {𝑆 : Signature 𝓞 𝓥}{𝑩 : Algebra {𝑆 = 𝑆} α ρ}
  → Finitary 𝑆 → JoinIsChain 𝑩 ℓ
finitary⇒JoinIsChain fin θ φ = finitary⇒Gen⊆Chain θ φ fin
```
