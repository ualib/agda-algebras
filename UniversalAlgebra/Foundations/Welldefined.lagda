---
layout: default
title : Foundations.WellDefined module (The Agda Universal Algebra Library)
date : 2021-02-23
author: [the ualib/agda-algebras development team][]
---

\begin{code}

module Foundations.Welldefined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; Setω to Typeω )
open import Axiom.Extensionality.Propositional
                                  using () renaming ( Extensionality to funext )
open import Data.Fin.Base         using ( Fin ; fromℕ ; fromℕ<)
open import Data.Nat              using ( ℕ )
open import Data.Product          using ( swap ; _×_ ; _,_ )
open import Function.Base         using ( _$_ ; flip ; _∘_ ; id )
import Relation.Binary.PropositionalEquality as PE

open import Overture.Preliminaries using ( _≈_ )
open import Relations.Discrete     using ( Op )

private variable
 ι α β 𝓥 : Level

\end{code}

#### Strongly well-defined operations

We now describe an extensionality principle that seems weaker than function extensionality, but still (probably) not provable in [MLTT][]. (We address this and other questions  below.)  We call this the principle *strong well-definedness of operations*. We will encounter situations in which this weaker extensionality principle suffices as a substitute for function extensionality.

Suppose we have a function whose domain is a function type, say, `I → A`.  For example, inhabitants of the type `Op` defined above are such functions.  (Recall, the domain of inhabitants of type `Op I A := (I → A) → A` is `I → A`.)

Of course, operations of type `Op I A` are well-defined in the sense that equal inputs result in equal outputs.

\begin{code}

welldef : {A : Type α}{I : Type 𝓥}(f : Op A I) → ∀ u v → u ≡ v → f u ≡ f v
welldef f u v = PE.cong f

\end{code}

A stronger form of well-definedness of operations is to suppose that point-wise equal inputs lead to the same output.  In other terms, we could suppose that  for all `f : Op I A`, we have `f u ≡ f v` whenever `∀ i → u i ≡ v i` holds.  We call this formalize this notation in the following type.

\begin{code}

swelldef : ∀ ι α → Type (lsuc (α ⊔ ι))
swelldef ι α = ∀ {I : Type ι}{A : Type α}(f : Op A I)(u v : I → A)
 →             u ≈ v → f u ≡ f v

funext→swelldef : {α 𝓥 : Level} → funext 𝓥 α → swelldef 𝓥 α
funext→swelldef fe f u v ptweq = welldef f u v (fe ptweq)

SwellDef : Typeω
SwellDef = (𝓤 𝓥 : Level) → swelldef 𝓤 𝓥
\end{code}

There are certain situations in which a (seemingly) weaker principle than function extensionality suffices.

A stronger well-definedness of operations would be to suppose that point-wise equal inputs lead to the same output.  In other words, we could suppose that for all `f : (I → A) → A`, we have `f u ≡ f v` whenever `∀ i → u i ≡ v i` holds.

\begin{code}

swelldef' : ∀ ι α β → Type (lsuc (ι ⊔ α ⊔ β))
swelldef' ι α β = ∀ {I : Type ι} {A : Type α} {B : Type β}
 →                (f : (I → A) → B) {u v : I → A}
 →                u ≈ v → f u ≡ f v


funext' : ∀ α β → Type (lsuc (α ⊔ β))
funext' α β = ∀ {A : Type α }{B : Type β }{f g : A → B}
 →           (∀ x → f x ≡ g x)  →  f ≡ g


-- `funext ι α` implies `swelldef ι α β`        (Note the universe levels!)
funext'→swelldef' : funext' ι α → swelldef' ι α β
funext'→swelldef' fe f ptweq = PE.cong f (fe ptweq)


 -- `swelldef ι α (ι ⊔ α)` implies `funext ι α`   (Note the universe levels!)
swelldef'→funext' : swelldef' ι α (ι ⊔ α) → funext' ι α
swelldef'→funext' wd ptweq = wd _$_ ptweq
\end{code}

#### Questions

1. Does the converse `swelldef→funext` hold or is `swelldef` is strictly weaker than `funext`?
2. If `swelldef` is strictly weaker than `funext`, then can we prove it in MLTT?
3. If the answer to 2 is no in general, then for what types `I` can we prove `swelldef 𝓥 _ {I}`?

Partial answers are gleaned from the following.

Notice that the implication swelldef → funext holds *if* we restrict the universe level β to be `ι ⊔ α`.
This is because to go from swelldef to funext, we must apply the swelldef premise to the special case
in which `f` is the identify function on `I → A`, which of course has type `(I → A) → (I → A)`.

This is possible if we take `swelldef ι α (ι ⊔ α)` as the premise (so that we can assume `B` is `I → A`).

It is NOT possible if we merely assume `swelldef ι α β` for *some* β (not necessarily `ι ⊔ α`) and for some B (not necessarily `I → A`).

In the agda-algebras library, swelldef is used exclusively on operation type, so that B ≡ A.
I believe there is no way to prove that `swelldef ι α α` implies funext ι α.


#### New thoughts/ideas

It seems unlikely that we could prove swelldef in MLTT because, on the face of it,
to prove f u ≡ f v, we need u ≡ v, but we only have ∀ i → u i ≡ v i.

\begin{code}

module _ {ι α β : Level} where

 swelldef-proof : ∀ {I : Type ι}{A : Type α}{B : Type β}
  →                 (f : (I → A) → B){u v : I → A}
  →                 (∀ i → u i ≡ v i) → f u ≡ f v

 swelldef-proof {I = I}{A}{B} f {u}{v} x = {!!}  --   <== we seem to be stuck here

\end{code}

However, we *can* prove swelldef in MLTT, for certain types at least,
using a sort of zipper lemma.

The idea is to partially apply f, and inductively build up a proof of f u ≡ f v like
a zipper.

1.     f (u 0)            ≡ f (v 0)            (by u 0 ≡ v 0),
2.     f (u 0)(u 1)       ≡ f (v 0)(v 1)       (by 1. and u 1 ≡ v 1),
...
n.     f (u 0)...(u(n-1)) ≡ f (v 0)...(v(n-1)) (by n-1 and u(n-1) ≡ v(n-1)).
...


Actually, the proof probably has to go in the other direction, like this:

...
n.     f (u 0)...(u(n-2))(u(n-1)) ≡ f (u0)...(u(n-2))(v(n-1))
n-1.   f (u 0)   (u(n-2))(u(n-1)) ≡ f (v 0)  (v(n-2))(v(n-1))
...
1.     f (u 0)(u 1)...            ≡ f (v 0)(v 1)...
...

Clearly this will work for finitary f.  What about for countable and arbitrary arities?

Here we prove the case when f : A → A → B (so f is essentially of operation type (Fin 2 → A) → B, binite case (well, Fin 2, but Fin n for any n should be an easy generalization of this).

\begin{code}

module _ {ι α β : Level} {A : Type α}{B : Type β} where

 open Fin renaming ( zero to fzer ; suc to fsuc )

 0' 1' : Fin 2
 0' = Fin.zero
 1' = Fin.suc Fin.zero

 open PE.≡-Reasoning
 Fin2-wd : (f : A → A → B)(u v : Fin 2 → A)
  →        u ≈ v → f (u fzer) (u (fsuc fzer)) ≡ f (v fzer) (v (fsuc fzer))
 Fin2-wd f u v uivi = Goal
  where
  ξ : u fzer ≡ v fzer
  ξ = uivi fzer
  ζ : u (fsuc fzer) ≡ v (fsuc fzer)
  ζ = uivi (fsuc fzer)

  part1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  part1 refl = refl

  part2 : ∀ {x y b} → x ≡ y → f x b ≡ f y b
  part2 refl = refl

  Goal : f (u fzer) (u (fsuc fzer)) ≡ f (v fzer) (v (fsuc fzer))
  Goal = f (u fzer) (u (fsuc fzer)) ≡⟨ part1 (uivi (fsuc fzer)) ⟩
         f (u fzer) (v (fsuc fzer)) ≡⟨ part2 (uivi fzer) ⟩
         f (v fzer) (v (fsuc fzer)) ∎

 Fin2-swelldef : (f : (Fin 2 → A) → B)(u v : Fin 2 → A)
  →              u ≈ v → f u ≡ f v
 Fin2-swelldef f u v uv = Goal
  where
  cur : (curry3 f) (u fzer) (u (fsuc fzer)) ≡ (curry3 f) (v fzer) (v (fsuc fzer))
  cur = Fin2-wd (curry3 f) u v uv

  Goal : f u ≡ f v
  Goal = f u ≡⟨ {!!} ⟩
         (uncurry3 ∘ curry3) f u ≡⟨ {!!} ⟩
         (uncurry3 ∘ curry3) f u ≡⟨ {!!} ⟩
         f v ∎



\end{code}

