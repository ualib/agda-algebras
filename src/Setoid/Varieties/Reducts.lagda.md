---
layout: default
file: "src/Setoid/Varieties/Reducts.lagda.md"
title: "Setoid.Varieties.Reducts module"
date: "2026-06-14"
author: "the agda-algebras development team"
---

### Reduct classes of varieties

This is the [Setoid.Varieties.Reducts][] module of the [Agda Universal Algebra Library][].

Like its companion [Setoid.Varieties.Invariance][], this module lives in the `Setoid/`
foundation; reducts are in the domain of universal algebra.

Fix two signatures `𝑆₁`, `𝑆₂` and a signature morphism `φ : 𝑆₁ → 𝑆₂`.  The reduct functor
`reduct φ : Alg 𝑆₂ → Alg 𝑆₁` ([Setoid.Categories.Reduct][]) turns each `𝑆₂`-algebra
into an `𝑆₁`-algebra by remembering only the operations named by `φ`.

Given a **variety** `𝒱` of `𝑆₂`-algebras, this module studies the *reduct class*

    reduct φ 𝒱  =  { 𝑩 : 𝑩 ≅ reduct φ 𝑨 for some 𝑨 ∈ 𝒱 },

a class of `𝑆₁`-algebras, and asks, "under which of the operators `S`, `H`,
`P` is `reduct φ 𝒱` closed?"[^1]

At first glance, we might anticipate that `reduct φ 𝒱` is closed under `S` and `P`
but not `H`, which would make it a *prevariety*.[^2]

Working it through against the library's definitions shows that the truth is different,
and sharper, so we record it formally here.  (This is research-tracking, where
discovering which assertion is the correct one is part of the process.)

Two layers must be distinguished.

+  **Functorial preservation (true for `S`, `P`, *and* `H`)**.  `reduct φ` preserves
   the subalgebra relation, products, and the homomorphic-image relation
   *between individual algebras*.  A mono maps to a mono, a product to a product, an
   epi to an epi.  This is what "`reduct φ` preserves subobjects and limits" means,
   and it is exactly the morphism action of the functor `reductF` read off on the
   three kinds of homomorphism.  All three hold, with one-line proofs, because
   `reduct φ` keeps the underlying setoid map of a homomorphism unchanged and only
   reindexes the operation it must respect.

+  **Class-level closure (true for `P` only)**.  Whether the *class* `reduct φ (𝒱)` is closed
   under an operator `O` is the question whether every `O`-construction performed on reducts
   can be **reconstructed upstairs** — realized as the reduct of an `O`-construction inside
   `𝒱`.  For products this reconstruction always succeeds (`reduct-⨅` below): a product of
   reducts *is* the reduct of a product, because the dropped operations on a product are
   computed coordinate-by-coordinate and are therefore always available.  For subalgebras and
   homomorphic images it can fail, because a sub- or quotient-algebra of a reduct generally
   cannot be re-equipped with the operations `φ` forgot.

The upshot: `reduct φ (𝒱)` is closed under `P` (and isomorphism) but
**not, in general, under `S` or `H`**.  It is a *product class* (model theory calls
reducts of an elementary class *pseudo-elementary*), and is **not** a prevariety —
`S`-closure already fails.  A concrete `S`-counterexample is recorded in the final
section; the failure of `H` is discussed there too, including the instructive fact
that for the variety of groups `H`-closure happens to *hold*, so neither the issue's
"`S, P` yes, `H` no" pattern nor its mirror is the general truth: the general truth
is "`P` always; `S` and `H` not in general."

There is a genuine grain of truth behind "prevariety", supplied by reduct-invariance of
satisfaction (`⊧-reduct`): every reduct of a `𝒱`-algebra satisfies the `φ`-pullback of
`𝒱`'s equational theory, so `reduct φ (𝒱)` is *contained in* a variety of `𝑆₁`-algebras even
though it need not equal one.  That containment is `reduct-⊧` below.

```agda
{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Overture using ( 𝓞 ; 𝓥 ; Signature )

module Setoid.Varieties.Reducts where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------
open import Data.Product                   using ( _,_ ; Σ-syntax ; proj₁ ; proj₂ )
                                           renaming ( _×_ to _∧_ )
open import Function                       using ( Func ; _∘_ )
open import Level                          using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary                using ( Setoid )
open import Relation.Unary                 using ( Pred ; _∈_ ; _⊆_ )

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Setoid.Algebras.Reduct             using  ( reduct )
open import Setoid.Categories.Reduct             using  ( reductF )
open import Setoid.Varieties.Invariance          using  ( ⊧-reduct )
open import Overture.Signatures.Morphisms           using  ( SigMorphism )
                                                    renaming ( ι to ι-op ; κ to κ-ar )
open import Overture.Terms                          using  ( Term )
open import Overture.Terms.Translation              using  ( _✶_ )
open import Setoid.Algebras.Basic                   using  ( Algebra ; 𝔻[_] )
open import Setoid.Algebras.Products                using  ( ⨅ )
open import Setoid.Homomorphisms.Basic              using  ( hom ; IsHom ; mkIsHom )
open import Setoid.Homomorphisms.Isomorphisms       using  ( _≅_ ; mkiso ; ≅-refl
                                                           ; ≅-sym ; ≅-trans ; ⨅≅ )
open import Setoid.Homomorphisms.HomomorphicImages  using  ( _IsHomImageOf_ )
open import Setoid.Subalgebras.Subalgebras          using  ( _≤_ )
open import Setoid.Categories.Functor               using  ( Functor )
open import Setoid.Varieties.Closure                using  ( P )

open IsHom using ( compatible )
open _≅_ using ( to ; from ; to∼from ; from∼to )

import Setoid.Varieties.EquationalLogic as EqLogic

private variable
  α ρ β ρᵇ γ ρᶜ ℓ ι χ : Level
```

#### Reduct preserves homomorphisms

Everything rests on one observation: a homomorphism is preserved by `reduct φ` *on the nose*.
Concretely, if `h : 𝑨 ⟶ 𝑩` is an `𝑆₂`-homomorphism, the very same underlying setoid map is an
`𝑆₁`-homomorphism `reduct φ 𝑨 ⟶ reduct φ 𝑩`.  The reason is definitional: `reduct φ`
interprets an `𝑆₁`-symbol `o` as the interpretation in `𝑨` of `ι φ o` precomposed with the
`κ φ o`-reindex, and `h` already respects every `𝑆₂`-operation — in particular `ι φ o` — so it
respects the reindexed one with no extra work.  This is the morphism action `F₁` of the functor
`reductF` ([Setoid.Categories.Reduct][]); we restate it directly here because the closure
arguments need it between algebras at *different* universe levels (subalgebra, isomorphism and
homomorphic-image relations are all level-heterogeneous), whereas `reductF` is the
single-level packaging.

```agda
module _ {𝑆₁ 𝑆₂ : Signature 𝓞 𝓥} (φ : SigMorphism 𝑆₁ 𝑆₂) where
  -- the signature's level bump, pinned to the module's `𝓞`/`𝓥` (no stray implicits).
  private
    ov : Level → Level
    ov ℓ = 𝓞 ⊔ 𝓥 ⊔ lsuc ℓ

  reduct-hom : {𝑨 : Algebra {𝑆 = 𝑆₂} α ρ}{𝑩 : Algebra {𝑆 = 𝑆₂} β ρᵇ}
    → hom 𝑨 𝑩 → hom (reduct φ 𝑨) (reduct φ 𝑩)
  reduct-hom (h , hhom) =
    h , mkIsHom (λ {o}{a} → compatible hhom {f = ι-op φ o} {a = a ∘ κ-ar φ o})
```

The single-level instance agrees with the functor's morphism map definitionally — they are the
same construction — which we record to make the dependence on `reductF` explicit.

```agda
  reduct-hom≡F₁ : {𝑨 𝑩 : Algebra {𝑆 = 𝑆₂} α ρ}(h : hom 𝑨 𝑩)
    → reduct-hom h ≡ Functor.F₁ (reductF φ) h
  reduct-hom≡F₁ _ = refl
```

#### Reduct preserves subalgebras, isomorphisms, and homomorphic images

Each of the three relation-preservations is now immediate.  `reduct-hom` keeps the underlying
map identical, so injectivity, surjectivity and the isomorphism round-trip conditions — all of
which are statements *about the underlying map and the (unchanged) codomain setoid* — transfer
verbatim.  These are the honest content of "`reduct φ` preserves `S`, `P` and `H`": it carries
subobjects to subobjects, isomorphisms to isomorphisms, and epis to epis.

```agda
  -- reduct preserves the subalgebra relation (S, functorially).
  reduct-≤ : {𝑨 : Algebra {𝑆 = 𝑆₂} α ρ}{𝑩 : Algebra {𝑆 = 𝑆₂} β ρᵇ}
   →         𝑨 ≤ 𝑩 → reduct φ 𝑨 ≤ reduct φ 𝑩
  reduct-≤ (h , hinj) = reduct-hom h , hinj

  -- reduct preserves isomorphism.
  reduct-≅ : {𝑨 : Algebra {𝑆 = 𝑆₂} α ρ}{𝑩 : Algebra {𝑆 = 𝑆₂} β ρᵇ}
   →         𝑨 ≅ 𝑩 → reduct φ 𝑨 ≅ reduct φ 𝑩
  reduct-≅ A≅B = mkiso  (reduct-hom (to A≅B)) (reduct-hom (from A≅B))
                        (to∼from A≅B) (from∼to A≅B)

  -- reduct preserves the homomorphic-image relation (H, functorially).
  reduct-img : {𝑨 : Algebra {𝑆 = 𝑆₂} α ρ}{𝑩 : Algebra {𝑆 = 𝑆₂} β ρᵇ}
   →           𝑩 IsHomImageOf 𝑨 → reduct φ 𝑩 IsHomImageOf reduct φ 𝑨
  reduct-img (h , hsur) = reduct-hom h , hsur
```

#### Reduct preserves products

The product preservation is the one that lifts to a genuine *class-level* closure, so we state
it as an isomorphism.  The reduct of a product and the product of the reducts have the **same
carrier** (`reduct φ` never touches the domain) and interpret each `𝑆₁`-symbol identically: in
both, the `o`-operation acts coordinatewise as `ι φ o` of the factors, reindexed by `κ φ o` —
and reindexing commutes with the coordinate projections.  So the two algebras are equal on the
nose up to the identity map, and the isomorphism is built from it, with every law holding by the
product setoid's reflexivity.

```agda
  module _ {I : Type ι}(𝒜 : I → Algebra {𝑆 = 𝑆₂} α ρ) where

    reduct-⨅ : reduct φ (⨅ 𝒜) ≅ ⨅ (λ i → reduct φ (𝒜 i))
    reduct-⨅ = mkiso  ( idmap-to    , mkIsHom (λ {o}{a} → Setoid.refl 𝔻[ ⨅R ]) )
                      ( idmap-from  , mkIsHom (λ {o}{a} → Setoid.refl 𝔻[ R⨅ ]) )
                      (λ b → Setoid.refl 𝔻[ ⨅R ])
                      (λ a → Setoid.refl 𝔻[ R⨅ ])
     where
     R⨅ : Algebra {𝑆 = 𝑆₁} (α ⊔ ι) (ρ ⊔ ι)
     R⨅ = reduct φ (⨅ 𝒜)
     ⨅R : Algebra {𝑆 = 𝑆₁} (α ⊔ ι) (ρ ⊔ ι)
     ⨅R = ⨅ (λ i → reduct φ (𝒜 i))
     -- `R⨅` and `⨅R` have definitionally equal domains, so the identity map is a
     -- homomorphism in both directions; its compatibility and the round-trips are refl.
     idmap-to : Func 𝔻[ R⨅ ] 𝔻[ ⨅R ]
     idmap-to = record { to = λ x → x ; cong = λ x≈y → x≈y }
     idmap-from : Func 𝔻[ ⨅R ] 𝔻[ R⨅ ]
     idmap-from = record { to = λ x → x ; cong = λ x≈y → x≈y }
```

#### The reduct image and closure under `P`

The *reduct image* `Reduct[ 𝒲 ]` of a class `𝒲` of `𝑆₂`-algebras is the class of
`𝑆₁`-algebras isomorphic to the reduct of some member of `𝒲`.  Closing under
isomorphism (rather than taking the bare set-image) is what makes it a *class* in the
sense the closure operators expect — `S`, `H`, `P` all produce iso-closed classes —
and it is the only honest notion under setoid semantics, where "the same algebra"
means "isomorphic".

```agda
  Reduct[_] :  Pred (Algebra {𝑆 = 𝑆₂} γ ρᶜ) ℓ
    → Pred (Algebra {𝑆 = 𝑆₁} β ρᵇ) (ov (γ ⊔ ρᶜ) ⊔ ℓ ⊔ β ⊔ ρᵇ)
  Reduct[ 𝒲 ] 𝑩 = Σ[ 𝑨 ∈ Algebra _ _ ] (𝑨 ∈ 𝒲) ∧ (𝑩 ≅ reduct φ 𝑨)
```

`Reduct[_]` is monotone: a bigger source class has a bigger reduct image.

```agda
  Reduct-mono :  {𝒲 𝒲' : Pred (Algebra {𝑆 = 𝑆₂} γ ρᶜ) ℓ}{𝑩 : Algebra {𝑆 = 𝑆₁} β ρᵇ}
    → 𝒲 ⊆ 𝒲' → 𝑩 ∈ Reduct[ 𝒲 ] → 𝑩 ∈ Reduct[ 𝒲' ]
  Reduct-mono 𝒲⊆𝒲' (𝑨 , 𝑨∈𝒲 , 𝑩≅r) = 𝑨 , 𝒲⊆𝒲' 𝑨∈𝒲 , 𝑩≅r
```

Now the class-level product result.  The clean, hypothesis-free statement is that the reduct
image **commutes past `P`**: a product of reduct-images is a reduct-image of a product,

    P Reduct[ 𝒱 ]  ⊆  Reduct[ P 𝒱 ].

The proof assembles the witnessing `𝒱`-algebras `𝓐` from the membership data of the factors,
takes their product `⨅ 𝓐` (a member of `P 𝒱` by construction), and chains three isomorphisms:
the given `𝑩 ≅ ⨅ 𝒞`, the product of the per-factor isos `⨅ 𝒞 ≅ ⨅ (reduct φ ∘ 𝓐)` (`⨅≅`), and
the product-preservation `⨅ (reduct φ ∘ 𝓐) ≅ reduct φ (⨅ 𝓐)` (`reduct-⨅`, reversed).

```agda
  P-Reduct : {𝒱 : Pred (Algebra {𝑆 = 𝑆₂} α ρ) (α ⊔ ρ ⊔ ov ℓ)}
    → P {α = α}{ρ}{α}{ρ} (α ⊔ ρ ⊔ ℓ) ι Reduct[ 𝒱 ] ⊆ Reduct[ P ℓ ι 𝒱 ]
  P-Reduct {α = α} {ρ} {𝒱 = 𝒱} {𝑩} ( I , 𝒞 , 𝒞∈R , 𝑩≅⨅𝒞 ) =
    ⨅ 𝓐 , (I , 𝓐 , 𝓐∈𝒱 , ≅-refl) , 𝑩≅red⨅𝓐
    where
    𝓐 : I → Algebra {𝑆 = 𝑆₂} α ρ
    𝓐 i = proj₁ (𝒞∈R i)
    𝓐∈𝒱 : ∀ i → 𝓐 i ∈ 𝒱
    𝓐∈𝒱 i = proj₁ (proj₂ (𝒞∈R i))
    𝒞≅red𝓐 : ∀ i → 𝒞 i ≅ reduct φ (𝓐 i)
    𝒞≅red𝓐 i = proj₂ (proj₂ (𝒞∈R i))
    𝑩≅red⨅𝓐 : 𝑩 ≅ reduct φ (⨅ 𝓐)
    𝑩≅red⨅𝓐 = ≅-trans 𝑩≅⨅𝒞 (≅-trans (⨅≅ 𝒞≅red𝓐) (≅-sym (reduct-⨅ 𝓐)))
```

This is the substance of "`reduct φ (𝒱)` is closed under products".  The final step —
concluding `P (Reduct[ 𝒱 ]) ⊆ Reduct[ 𝒱 ]` itself when `𝒱` is a variety — combines
`P-Reduct` with `Reduct-mono` and the `P`-closure of `𝒱`: `P 𝒱 ⊆ 𝒱`; the only
remaining gap is the universe-level bump that products introduce (`⨅ 𝓐` lands one
level up), which the library bridges with `Lift-Alg` and `Level-closure`
([Setoid.Varieties.Closure][]) exactly as it does for the HSP theorem.
We stop at `P-Reduct`, the level-clean heart of the matter, in keeping with the
bounded, research-tracking scope of this milestone.

#### Reducts satisfy the pulled-back theory

The genuine grain of truth behind "prevariety" is supplied by reduct-invariance of satisfaction
(`⊧-reduct`, [Setoid.Varieties.Invariance][]).  For any family `ℰ` of `𝑆₁`-equations, if an
`𝑆₂`-algebra `𝑨` satisfies every `φ`-*translated* equation `φ ✶ s ≈ φ ✶ t`, then its reduct
satisfies the original family.  In closure-operator terms this says

    reduct φ (Mod (φ ✶ ℰ))  ⊆  Mod ℰ,

so the reduct image of a variety is *contained in* a variety of `𝑆₁`-algebras (the model class
of the pulled-back theory).  That is the precise, true residue of the prevariety intuition: the
reduct class is cut out from a variety by equations — it simply need not be all of that variety,
nor closed under `S`.

```agda
  module _
    {X : Type χ}{I : Type ι}
    (ℰ : I → Term {𝑆 = 𝑆₁} X ∧ Term {𝑆 = 𝑆₁} X)
    (𝑨 : Algebra {𝑆 = 𝑆₂} α ρ)
    where
    open EqLogic {𝑆 = 𝑆₁} using () renaming ( _⊧_≈_ to _⊧₁_≈_ )
    open EqLogic {𝑆 = 𝑆₂} using () renaming ( _⊧_≈_ to _⊧₂_≈_ )

    reduct-⊧ : (∀ i → 𝑨 ⊧₂ (φ ✶ proj₁ (ℰ i)) ≈ φ ✶ proj₂ (ℰ i))
      → ∀ i → reduct φ 𝑨 ⊧₁ proj₁ (ℰ i) ≈ proj₂ (ℰ i)
    reduct-⊧ A⊧ i = ⊧-reduct φ 𝑨 {s = proj₁ (ℰ i)} {t = proj₂ (ℰ i)} (A⊧ i)
```

#### Why `S` and `H` fail at the class level

It remains to substantiate the claim that `reduct φ 𝒱` is **not** closed under `S`
(and, in general, not under `H`), so it is a product class rather than a prevariety.
The asymmetry with `P` is structural: the functorial preservations above all run
`𝑆₂ → 𝑆₁` (reduct of a subalgebra is a subalgebra, etc.), but *class-level* closure
needs the reverse, `𝑆₁ → 𝑆₂`, **reconstruction** — every
`𝑆₁`-subalgebra/quotient/product of a reduct must arise as the reduct of an
`𝑆₂`-subalgebra/quotient/product inside `𝒱`.

For products that reconstruction is automatic (`reduct-⨅`): the dropped operations on
a product are computed coordinatewise from the factors, so they are always present.

For subalgebras and quotients it can fail, because a sub- or quotient-algebra of a
reduct generally cannot be re-equipped with the operations `φ` forgot.

Categorically: `reduct φ` is a right adjoint — `F ⊣ reduct φ` — so it preserves
limits, which is why products are the well-behaved case.

##### Counterexamples

1.  Let `𝑆₂` be the group signature with binary `·`, unary `⁻¹`, and nullary `e`; let
    `𝑆₁` be the monoid signature with binary `·` and nullary `e`; let `φ : 𝑆₁ ↪ 𝑆₂`
    be the natural inclusion; then `reduct φ` forgets `⁻¹` keeping `·` and `e`.  Take
    `𝒱` to be the variety of groups.  Then `reduct φ 𝒱` is the class of monoid
    reducts of 𝒱 — monoids `(M , ·, e)` such that `(M , ·, ⁻¹, e)` forms a group.

    +  The monoid `(ℤ , + , 0)` is a reduct of the group `(ℤ , + , - , 0)`, so
       `(ℤ , + , 0) ∈ reduct φ 𝒱`.
    +  As monoids, `(ℕ , + , 0) ≤ (ℤ , + , 0)` — `ℕ` is closed under `+` and the
       inclusion is an injective monoid homomorphism — so `(ℕ , + , 0) ∈ S (reduct φ 𝒱)`.
    +  But `(ℕ , + , 0)` is *not* a monoid reduct of some group; there is no group whose
       carrier is `ℕ` and whose binary operation is `+`, since any nonzero natural number
       has no additive inverse in `ℕ`, so `(ℕ , + , 0) ∉ reduct φ 𝒱`.

    This proves that `S (reduct φ 𝒱) ⊈ reduct φ 𝒱`, so `reduct φ 𝒱` is not closed under
    `S`, and therefore is not a prevariety.

    Stated against the operator, the false inclusion is `S Reduct[ 𝒱 ] ⊆ Reduct[ S 𝒱 ]`;
    it would require a sub-monoid of a group to be the reduct of a subgroup, which
    `ℕ ⊆ ℤ` refutes.

2.  Class-level `H`-closure, `H Reduct[ 𝒱 ] ⊆ Reduct[ H 𝒱 ]`, also fails in general,
    for the same reconstruction reason: the kernel of a surjective `𝑆₁`-homomorphism
    out of a reduct is an `𝑆₁`-congruence, but need not be an `𝑆₂`-congruence, so the
    quotient need not carry the dropped operations.  Notably, for the group example
    above it happens to *hold* — every monoid-congruence of a group is a
    group-congruence (from `a θ b` one derives `b⁻¹ θ a⁻¹` by multiplying on both
    sides), so a monoid-quotient of a group is again a group-monoid.

In short, `reduct φ 𝒱` is a product-closed (pseudo-elementary) class, contained in a
variety by `reduct-⊧`, but is not a prevariety.

--------------------------------------

[^1]: The closure operators `H`, `S`, and `P` are defined in the [Setoid.Varieties.Closure][] module.

[^2]: This was indeed what GitHub Issue [#345](https://github.com/ualib/agda-algebras/issues/345) proposed, prompting this exploration of the reduct functor in a submodule of the `Varieties`{.AgdaModule} module.

{% include UALib.Links.md %}
