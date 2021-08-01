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
open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Primitive        using ( _⊔_ ; lsuc ; Level ) renaming ( Set to Type ; Setω to Typeω )
open import Axiom.Extensionality.Propositional
                                  using () renaming ( Extensionality to funext )
open import Data.Fin.Base         using ( Fin ; toℕ)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_ ; _≤_ ; s≤s)
open import Data.Product                using ( _,_ ; _×_ )
open import Data.List.Base        using ( lookup ; length ; [_] ; _++_; head ; tail)
open import Data.List.Properties  using ( ≡-dec )
open import Function.Base         using ( _$_ ; _∘_ ; id )
open import Relation.Binary       using ( Rel )
open import Relation.Binary.Definitions  using ( DecidableEquality )
import Relation.Binary.PropositionalEquality as PE


open import Overture.Preliminaries using ( _≈_ ; _⁻¹)
open import Relations.Discrete     using ( Op )
open import Overture.Transformers  using ( CurryFin2 ; UncurryFin2 ; UncurryFin3 ; A×A→Fin2A ; Fin2A→A×A
                                         ; A×A→B-to-Fin2A→B ; A→A→Fin2A ; Fin2A→B-to-A×A→B
                                         ; A×A~Fin2A-pointwise ; A→A~Fin2A-pointwise )

private variable
 ι α β 𝓥 ρ : Level

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

 open Fin renaming ( zero to z ; suc to s )
 open PE.≡-Reasoning

 A×A-wd : (f : A × A → B)(u v : Fin 2 → A)
  →        u ≈ v → (A×A→B-to-Fin2A→B f) u ≡ (A×A→B-to-Fin2A→B f) v

 A×A-wd f u v u≈v = Goal
  where
  zip1 : ∀ {a x y} → x ≡ y → f (a , x) ≡ f (a , y)
  zip1 refl = refl

  zip2 : ∀ {x y b} → x ≡ y → f (x , b) ≡ f (y , b)
  zip2 refl = refl

  Goal : (A×A→B-to-Fin2A→B f) u ≡ (A×A→B-to-Fin2A→B f) v
  Goal = (A×A→B-to-Fin2A→B f) u     ≡⟨ refl ⟩
         f (u z , u (s z)) ≡⟨ zip1 (u≈v (s z)) ⟩
         f (u z , v (s z)) ≡⟨ zip2 (u≈v z) ⟩
         f (v z , v (s z)) ≡⟨ refl ⟩
         (A×A→B-to-Fin2A→B f) v ∎

 Fin2-wd : (f : A → A → B)(u v : Fin 2 → A)
  →        u ≈ v → (UncurryFin2 f) u ≡ (UncurryFin2 f) v

 Fin2-wd f u v u≈v = Goal
  where
  zip1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  zip1 refl = refl

  zip2 : ∀ {x y b} → x ≡ y → f x b ≡ f y b
  zip2 refl = refl

  Goal : (UncurryFin2 f) u ≡ (UncurryFin2 f) v
  Goal = (UncurryFin2 f) u     ≡⟨ refl ⟩
         f (u z) (u (s z)) ≡⟨ zip1 (u≈v (s z)) ⟩
         f (u z) (v (s z)) ≡⟨ zip2 (u≈v z) ⟩
         f (v z) (v (s z)) ≡⟨ refl ⟩
         (UncurryFin2 f) v ∎

 -- Fin2-wd' : (f : (List A) → B)(u v : List A)
 --  →        (all ∀ i → (loou ≈ v → f u ≡ f v

 -- Fin2-wd' f u v u≈v = {!!}
  -- where
  -- zip1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  -- zip1 refl = refl
  -- Goal : f u ≡ f v
  -- Goal = {!!}
  -- zip1 : ∀ {a x y} → x ≡ y → f a x ≡ f a y
  -- zip1 refl = refl

  -- zip2 : ∀ {x y b} → x ≡ y → f x b ≡ f y b
  -- zip2 refl = refl

  -- Goal : f (λ {z → u z ; (s z) → u (s z)}) ≡ f (λ {z → v z ; (s z) → v (s z)})
  -- Goal = {!!} -- f (λ {z → u z ; (s z) → u (s z)}) ≡⟨ {!!} ⟩ 
         -- (CurryFin2 f) (u z) (u (s z)) ≡⟨ {!!} ⟩ -- zip1 (u≈v (s z)) ⟩
         -- (CurryFin2 f) (u z) (v (s z)) ≡⟨ {!!} ⟩ -- zip2 (u≈v z) ⟩
         -- (CurryFin2 f) (v z) (v (s z)) ≡⟨ {!!} ⟩
         -- f (λ {z → v z ; (s z) → v (s z) }) ∎




 Fin3-wd : (f : A → A → A → B)(u v : Fin 3 → A)
  →        u ≈ v → (UncurryFin3 f) u ≡ (UncurryFin3 f) v

 Fin3-wd f u v u≈v = Goal
  where

  zip1 : ∀ {a b x y} → x ≡ y → f a b x ≡ f a b y
  zip1 refl = refl

  zip2 : ∀ {a b x y} → x ≡ y → f a x b ≡ f a y b
  zip2 refl = refl

  zip3 : ∀ {a b x y} → x ≡ y → f x a b ≡ f y a b
  zip3 refl = refl

  Goal : (UncurryFin3 f) u ≡ (UncurryFin3 f) v
  Goal = (UncurryFin3 f) u     ≡⟨ refl ⟩
         f (u z) (u (s z)) (u (s (s z))) ≡⟨ zip1 (u≈v (s (s z))) ⟩
         f (u z) (u (s z)) (v (s (s z))) ≡⟨ zip2 (u≈v (s z)) ⟩
         f (u z) (v (s z)) (v (s (s z))) ≡⟨ zip3 (u≈v z) ⟩
         f (v z) (v (s z)) (v (s (s z))) ≡⟨ refl ⟩
         (UncurryFin3 f) v ∎


 -- NEXT: try to prove (f : (Fin 2 → A) → B)(u v : Fin 2 → A) →  u ≈ v → f u ≡ f v

module _ {A : Type α}{B : Type β} where -- {de : DecidableEquality A} where

 ListA→B : (f : List A → B)(u v : List A)
  →        u ≡ v → f u ≡ f v
 ListA→B f u .u refl = refl

 -- lookup⁻ : length xs ≡ length ys →
 --          (∀ {i j} → toℕ i ≡ toℕ j → R (lookup xs i) (lookup ys j)) →
 --          Pointwise R xs ys
 -- →        ( ∀ i j → i ≡ j → (lookup u) i ≡ (lookup v) j )

 CurryListA : (List A → B) → (List A → A → B)
 CurryListA f [] a = f [ a ]
 CurryListA f (x ∷ l) a = f ((x ∷ l) ++ [ a ]) 

 CurryListA' : (List A → B) → (A → List A → B)
 CurryListA' f a [] = f [ a ]
 CurryListA' f a (x ∷ l) = f ([ a ] ++ (x ∷ l))



 -- ListA→B-dec : (f : List A → B)(u v : List A)
 --  →        (length u) ≡ (length v)
 --  →        ( ∀ {i j} → toℕ i ≡ toℕ j → (lookup u i) ≡ (lookup v j ))
 --  →        f u ≡ f v
 -- ListA→B-dec f u v x y = {!Goal!}
 --  where
 --  zip1 : (CurryListA' f) (head u) (tail u) ≡ f u
 --  zip1 = ?
 --  Goal : f u ≡ f v
 --  Goal = {!!}





\end{code}




-------------------------------------

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team





















 -- It seems `Fin n → A` does not behave as we would home and expect.
 -- Instead, try using Vector A n, or try defining our own finite type FinTyp n.

 -- Fin2-unc∘cur≈id : (f : (Fin 2 → A) → B) → (UncurryFin2 ∘ CurryFin2) f ≡ f
 -- Fin2-unc∘cur≈id f = {!!}

 -- Fin2-swelldef : (f : (Fin 2 → A) → B)(u v : Fin 2 → A) → u ≈ v → f u ≡ f v
 -- Fin2-swelldef f u v u≈v = f u                           ≡⟨ PE.cong-app ((Fin2-unc∘cur≈id f)⁻¹) u ⟩
 --                           (UncurryFin2 (CurryFin2 f)) u ≡⟨ Fin2-wd (CurryFin2 f) u v u≈v ⟩
 --                           (UncurryFin2 (CurryFin2 f)) v ≡⟨ PE.cong-app (Fin2-unc∘cur≈id f) v ⟩
 --                           f v ∎
