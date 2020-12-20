\begin{code}
-- FILE: basic.agda
-- AUTHOR: William DeMeo and Siva Somayyajula
-- DATE: 30 Jun 2020
-- Note: This was used for the second part of my talk at JMM Special Session.

{-# OPTIONS --without-K --exact-split --safe #-}

module basic where

-- modules that import basic:
-- congruences, homomorphisms, terms, subuniverses, closure, birkhoff

open import prelude using (Universe; 𝓘; 𝓞; 𝓤; 𝓤₀;𝓥; 𝓦; 𝓣; 𝓧; 𝓤ω; Σω; _⸲_; is-set;
  _⁺; _̇;_⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Epic; Pred; _∈_) public

--The type of operations
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A

--Example. the projections
π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
π i x = x i

--𝓞 is the universe in which operation symbols live
--𝓥 is the universe in which arities live
Signature : (𝓞 𝓥 : Universe) → (𝓞 ⊔ 𝓥) ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇ )
-- -Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-- -Σ X Y = Σ Y
--𝓞 is the universe in which operation symbol types live
--𝓥 is the universe in which arity types live
--Recall,
-- -Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-- -Σ X Y = Σ Y
\end{code}

### Sets (or 0-groupoids)
Before defining the type of algebras, we need to explain what it means to be a set in univalent mathematics.  A type is defined to be a **set** if there is at most one way for any two of its elements to be equal.

MHE defines this notion (e.g., in the MGS-Embeddings module) as follows:

```agda
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

and explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."

### Types for Algebras

The first type for representing algebras that we define will put the domain of an algebra in an arbitrary type.  We will call these "∞-algebras" because the universe need not be a set.  After that, we define the type of algebra that we typically think of when doing informal universal algebra, which we call "0-algebras" since their domains are sets.

\begin{code}
∞-algebra Algebra : (𝓤 : Universe){𝓞 𝓥 : Universe}
          (𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

∞-algebra 𝓤 {𝓞}{𝓥} 𝑆 = Σ A ꞉ 𝓤 ̇ , ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)
Algebra = ∞-algebra

0-algebra : (𝓤 : Universe){𝑆 : Signature 𝓤 𝓤} → 𝓤 ⁺ ̇
0-algebra 𝓤{𝑆} = Σ A ꞉ 𝓤 ̇ , is-set A × ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)

data monoid-op : 𝓤₀ ̇ where
 e : monoid-op
 · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }


module _ {𝑆 : Signature 𝓞 𝓥}  where


 _̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

 ⨅ : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅ {𝓘}{𝓤}{I} 𝒜 =
  ((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}

 ⊓ : {𝓤 : Universe}{I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra 𝓤 𝑆
 ⊓ {𝓤} = ⨅ {𝓤}{𝓤}

 {- Usually we want to assume that, given an algebra 𝑨, we can always find a surjective
    map h₀ : X → ∣ 𝑨 ∣ from an arbitrary collection X of "variables" onto the universe of 𝑨.
    Here is the type we use when making this assumption. -}

 _↠_ : {𝓤 𝓧 : Universe} → 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
 X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h
\end{code}

### Algebras as record types

Sometimes it's more convenient to use records than sigma types. For such cases, we might prefer the following representation of the type of algebras.

\begin{code}
record algebra (𝓤 : Universe){𝓞 𝓥 : Universe} (𝑆 : Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)) : (𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺ ̇ where
 constructor mkalg
 field
  univ : 𝓤 ̇
  op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ

open algebra

module _ {𝓞 𝓥 : Universe} {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where
 ⨅' : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → algebra 𝓤 𝑆) → algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅' {𝓘}{𝓤}{I} 𝒜 = record
                    { univ = (i : I) → univ (𝒜 i)
                    ; op = λ(f : ∣ 𝑆 ∣)
                            (𝒂 : ∥ 𝑆 ∥ f → (j : I) → univ(𝒜 j))
                            (i : I) → ((op (𝒜 i)) f)
                            λ{x → 𝒂 x i}
                    }
\end{code}

One of the most painful aspects of Agda's flexible hierarchy of universe levels is that we will often be faced with errors of the following kind:

```agda
```

To make these situations easier to deal with, we provide some domain specific tools for the lifting and lowering of universe levels of our types.  We must do this with some care to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

First, a general `Lift` record type, similar to the one found in the Agda std lib `Level` module, is defined as follows.
<!-- source: http://www.cse.chalmers.se/~nad/repos/lib/src/Level.agda -->
<!-- accessed: 19 Dec 2020 -->
\begin{code}
record Lift {𝓤 𝓦 : Universe} (X : 𝓤 ̇) : 𝓤 ⊔ 𝓦 ̇  where
 constructor lift
 field lower : X
open Lift
\end{code}
Next, we give various ways to lift function types.
\begin{code}
lift-dom : {𝓧 𝓨 𝓦 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓧}{𝓦} X → Y)
lift-dom f = λ x → (f (lower x))

lift-cod : {𝓧 𝓨 𝓦 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (X → Lift{𝓨}{𝓦} Y)
lift-cod f = λ x → lift (f x)

lift-fun : {𝓧 𝓨 𝓦 𝓩 : Universe}{X : 𝓧 ̇}{Y : 𝓨 ̇} → (X → Y) → (Lift{𝓧}{𝓦} X → Lift{𝓨}{𝓩} Y)
lift-fun f = λ x → lift (f (lower x))
\end{code}
Now, getting more "domain-specific," we show how to lift algebraic operation types and then, finally, algebra types themselves.
\begin{code}
module _ {𝓞 𝓥 : Universe} {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where

 lift-op : {𝓤 : Universe}{I : 𝓥 ̇}{A : 𝓤 ̇}
  →        ((I → A) → A) → (𝓦 : Universe)
  →        ((I → Lift{𝓤}{𝓦}A) → Lift{𝓤}{𝓦}A)
 lift-op f 𝓦 = λ x → lift (f (λ i → lower (x i)))

 lift-alg-record-type : {𝓤 : Universe} → algebra 𝓤 𝑆 → (𝓦 : Universe) → algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-alg-record-type 𝑨 𝓦 = mkalg (Lift (univ 𝑨)) (λ (f : ∣ 𝑆 ∣) → lift-op ((op 𝑨) f) 𝓦)

 lift-∞-algebra lift-alg : {𝓤 : Universe} → Algebra 𝓤 𝑆 → (𝓦 : Universe) → Algebra (𝓤 ⊔ 𝓦) 𝑆
 lift-∞-algebra 𝑨 𝓦 = Lift ∣ 𝑨 ∣ , (λ (f : ∣ 𝑆 ∣) → lift-op (∥ 𝑨 ∥ f) 𝓦)
 lift-alg = lift-∞-algebra

\end{code}
