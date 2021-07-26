---
layout: default
title : Foundations.Welldefined module (The Agda Universal Algebra Library)
date : 2021-07-25
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Foundations.Welldefined where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; Setω to Typeω )
open import Axiom.Extensionality.Propositional
                                  using () renaming ( Extensionality to funext )
open import Data.Fin.Base         using ( Fin )
open import Function.Base         using ( _$_ )
import Relation.Binary.PropositionalEquality as PE


open import Overture.Preliminaries using ( _≈_ )
open import Relations.Discrete     using ( Op )
open import Overture.Inverses      using ( UncurryFin )

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


-- universe-level-polymorphic version
SwellDef : Typeω
SwellDef = (α β : Level) → swelldef α β
\end{code}

There are certain situations in which a (seemingly) weaker principle than function extensionality suffices.

Here are the more general versions of the foregoing that are not restricted to (I-ary) *operations* on A (of type (I → A) → A), but handle also (I-ary) *functions* from A^I to B (of type (I → A) → B).

\begin{code}

swelldef' : ∀ ι α β → Type (lsuc (ι ⊔ α ⊔ β))
swelldef' ι α β = ∀ {I : Type ι} {A : Type α} {B : Type β}
 →                (f : (I → A) → B) {u v : I → A}
 →                u ≈ v → f u ≡ f v


funext' : ∀ α β → Type (lsuc (α ⊔ β))
funext' α β = ∀ {A : Type α } {B : Type β } {f g : A → B}
 →            f ≈ g → f ≡ g


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

-- swelldef-proof : ∀ {I : Type ι}{A : Type α}{B : Type β}
--  →                 (f : (I → A) → B){u v : I → A}
--  →                 (∀ i → u i ≡ v i) → f u ≡ f v
-- swelldef-proof {I = I}{A}{B} f {u}{v} x = {!!}  --   <== we are stuck

\end{code}

HOWEVER, we *can* prove swelldef in MLTT for certain types at least, using a zipper argument.

This certainly works in the special case of *finitary* functions, say,
`f : (Fin n → A) → B` for some n.

I expect this proof will generalize to countable arities, but I have yet to formally prove it.

If f is finitary, then we can Curry and work instead with the function

(Curry f) : A → A → A → ... → A → B

(for some appropriate number of arrow; i.e., number of arguments).

The idea is to partially apply f, and inductively build up a proof of f u ≡ f v, like so.

1.     f (u 0)            ≡ f (v 0)            (by u 0 ≡ v 0),
2.     f (u 0)(u 1)       ≡ f (v 0)(v 1)       (by 1. and u 1 ≡ v 1),
...
n.     f (u 0)...(u(n-1)) ≡ f (v 0)...(v(n-1)) (by n-1 and u(n-1) ≡ v(n-1)).
...


Actually, the proof would probably go in the other direction, like so.

...
n.     f (u 0)...(u(n-2))(u(n-1)) ≡ f (u0)...(u(n-2))(v(n-1))
n-1.   f (u 0)   (u(n-2))(u(n-1)) ≡ f (v 0)  (v(n-2))(v(n-1))
...
1.     f (u 0)(u 1)...            ≡ f (v 0)(v 1)...
...

To formalize this, let's begin with the simplest case, that is, when f : A → A → B,
so f is essentially of type (Fin 2 → A) → B.

(HOWEVER, we still need to establish a one-to-one correspondence between the types
(Fin 2 → A) → B and A → A → B, (and A × A → B), which turns out to be nontrivial.)

\begin{code}

module _ {A : Type α}{B : Type β} where

 open Fin renaming ( zero to zz ; suc to ss )
 open PE.≡-Reasoning

 Fin2-wd : (f : A → A → B)(u v : Fin 2 → A)
  →        u ≈ v → (UncurryFin f) u ≡ (UncurryFin f) v

 Fin2-wd f u v u≈v = Goal
  where
  ξ : u zz ≡ v zz
  ξ = u≈v zz
  ζ : u (ss zz) ≡ v (ss zz)
  ζ = u≈v (ss zz)

  zip1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  zip1 refl = refl

  zip2 : ∀ {x y b} → x ≡ y → f x b ≡ f y b
  zip2 refl = refl

  Goal : (UncurryFin f) u ≡ (UncurryFin f) v
  Goal = (UncurryFin f) u     ≡⟨ refl ⟩
         f (u zz) (u (ss zz)) ≡⟨ zip1 (u≈v (ss zz)) ⟩
         f (u zz) (v (ss zz)) ≡⟨ zip2 (u≈v zz) ⟩
         f (v zz) (v (ss zz)) ≡⟨ refl ⟩
         (UncurryFin f) v ∎


 -- NEXT: try to prove (f : (Fin 2 → A) → B)(u v : Fin 2 → A) →  u ≈ v → f u ≡ f v

\end{code}




-------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
