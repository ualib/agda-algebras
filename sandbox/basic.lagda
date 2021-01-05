FILE: basic.agda
AUTHOR: William DeMeo and Siva Somayyajula
DATE: 30 Jun 2020
UPDATE: 3 Jan 2021

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module basic where

open import prelude using (Universe; 𝓞; 𝓥; 𝓘; 𝓤; 𝓤₀; 𝓦; 𝓧; _⸲_; is-set;
 _⁺; _̇; _⊔_; _,_; Σ; -Σ; ∣_∣; ∥_∥; 𝟘; 𝟚; _×_; Epic; Pred; _∈_; _∘_; _≡_; 𝑖𝑑; 𝓻ℯ𝓯𝓵) public

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
\end{code}

Recall, the definition of the type `Σ`.

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```

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
∞-algebra Algebra : (𝓤 : Universe)
          (𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

∞-algebra 𝓤  𝑆 = Σ A ꞉ 𝓤 ̇ , ((f : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f) A)
Algebra = ∞-algebra
\end{code}
The type of the `Algebra 𝓤 𝑆` type is `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇`. This type is used so often in our library that in some modules (where the signature universe levels 𝓞 𝓥 are already in context) we will define the following shorthand for the universe level:

```agda
OV : Universe → Universe
OV = λ 𝓤 → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)
```

so we can now simply type `OV 𝓤` in place of the more laborious `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.
\begin{code}

data monoid-op : 𝓤₀ ̇ where
 e : monoid-op
 · : monoid-op

monoid-sig : Signature _ _
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }
\end{code}


### Algebras as record types

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

\begin{code}
record algebra (𝓤 : Universe) (𝑆 : Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)) : (𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺ ̇ where
 constructor mkalg
 field
  univ : 𝓤 ̇
  op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ

open algebra
\end{code}
Of course, we can go back and forth between these two representations easily.
\end{code}
\begin{code}

module _ {𝑆 : Signature 𝓞 𝓥} where  -- {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)}

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥
\end{code}

### Products of algebras

Define here is a shorthand for the interpretation of an operation symbol and then products for algebras in the Sigma type representation (the one we use most) and the record type representation.

\begin{code}
module _ {𝑆 : Signature 𝓞 𝓥}  where

 _̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

 -- product for algebras of sigma type
 ⨅ : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅ {𝓘}{𝓤}{I} 𝒜 =
  ((i : I) → ∣ 𝒜 i ∣) , λ(f : ∣ 𝑆 ∣)(𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)(i : I) → (f ̂ 𝒜 i) λ{x → 𝒂 x i}

 ⊓ : {𝓤 : Universe}{I : 𝓤 ̇ }(𝒜 : I → Algebra 𝓤 𝑆 ) → Algebra 𝓤 𝑆
 ⊓ {𝓤} = ⨅ {𝓤}{𝓤}

 -- product for algebras of record type
 ⨅' : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → algebra 𝓤 𝑆) → algebra (𝓘 ⊔ 𝓤) 𝑆
 ⨅' {𝓘}{𝓤}{I} 𝒜 = record
                    { univ = (i : I) → univ (𝒜 i)
                    ; op = λ(f : ∣ 𝑆 ∣)
                            (𝒂 : ∥ 𝑆 ∥ f → (j : I) → univ(𝒜 j))
                            (i : I) → ((op (𝒜 i)) f)
                            λ{x → 𝒂 x i}
                    }
\end{code}
For example, if we have a class 𝒦 of algebras, defined as a predicate over algebras, then we define the product of all algebras in the class as follows.
\begin{code}
module class-product {𝓤 : Universe} {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)}{𝒦 : Pred (Algebra 𝓤 𝑆) (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)} where

 ov : Universe → Universe
 ov = λ 𝓤 → (𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺)

 ⨅'' : {𝓘 𝓤 : Universe}{I : 𝓘 ̇ }(𝒜 : I → Algebra 𝓤 𝑆) → algebra _ 𝑆
 ⨅'' {𝓘}{𝓤}{I} 𝒜 = record
                    { univ = (i : I) → ∣ 𝒜 i ∣
                    ; op = λ(f : ∣ 𝑆 ∣)
                            (𝒂 : ∥ 𝑆 ∥ f → (j : I) → ∣ 𝒜 j ∣)
                            (i : I) → ∥ 𝒜 i ∥ f
                            λ{x → 𝒂 x i}
                    }


 -- ℑ serves as the index of the product
 ℑ : {𝓤 : Universe} →  Pred (Algebra 𝓤 𝑆)(ov 𝓤) → (ov 𝓤) ̇
 ℑ {𝓤} 𝒦 = Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦

 -- 𝔄 produces an algebra for each index (i : ℑ).
 𝔄 : {𝓤 : Universe}{𝒦 : Pred (Algebra 𝓤 𝑆)(ov 𝓤)} → ℑ 𝒦 → Algebra 𝓤 𝑆
 𝔄{𝓤}{𝒦} = λ (i : (ℑ 𝒦)) → ∣ i ∣

 -- The product of all members of 𝒦 can be written simply as follows:
 class-product : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (ov 𝓤) 𝑆
 class-product {𝓤} 𝒦 = ⨅ ( 𝔄{𝓤}{𝒦} )

 -- ...or, more explicitly, here is the expansion of this indexed product.
 class-product' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (ov 𝓤) 𝑆
 class-product'{𝓤} 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦)) → ∣ i ∣

 class-product'' : {𝓤 : Universe} → Pred (Algebra 𝓤 𝑆)(ov 𝓤) → algebra (ov 𝓤) 𝑆
 class-product'' {𝓤} 𝒦 = ⨅''{ov 𝓤}{𝓤}{ℑ 𝒦} ( 𝔄{𝓤}{𝒦} ) --  ( 𝔄{𝓤}{𝒦} )

\end{code}
--If KA : 𝑨 ∈ 𝒦, then (𝑨 , KA) ∈ ℑ 𝒦, and the projection of the product onto 𝑨 is

### Universe level errors

The hierarchy of universe levels in Agda looks like this:

```agda

  𝓤₀ : 𝓤₁, 𝓤₁ : 𝓤₂, 𝓤₂ : 𝓤₃, …,
```
This means that the type level of `𝓤₀` is `𝓤₁`, and for each `n` The type level of `𝓤ₙ` is `𝓤ₙ₊₁.

It is important to note, however, that this does *not* imply 𝓤₀ : 𝓤₂ and 𝓤₀ : 𝓤₃ and so on.  In other words, Agda's universe hierarchy is *noncummulative*.  This makes it possible to treat universe levels more general and exercise more precise control over them, which is nice. On the other hand, in this author's experience, a noncummulative hierarchy can make for a nonfun proof assistant.

Luckily, there are ways to overcome this technical issue. We will describe some such techniques that we developed specifically for our domain of interest.

To be more concrete, noncummulativity of universe levels will frequently cause Agda to complain with errors like the following:

```agda
birkhoff.lagda:498,20-23
(𝓤 ⁺) != (𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)
when checking that the expression SP𝒦 has type
Pred (Σ (λ A → (f₁ : ∣ 𝑆 ∣) → Op (∥ 𝑆 ∥ f₁) A)) _𝓦_2346
```

First of all, we must know how to interpret such errors since they arises so often. The one above means that Agda encountered a type at universe level `𝓤 ⁺`, on line 498 (columns 20--23) of the file birkhoff.lagda file, but was expecting a type at level `(𝓞 ⁺) ⊔ (𝓥 ⁺) ⊔ ((𝓤 ⁺) ⁺)` instead.

To make these situations easier to deal with, we developed some domain specific tools for the lifting and lowering of universe levels of our algebra types. (Later we do the same for other domain specific types like homomorphisms, subalgebras, products, etc).  Of course, this must be done carefully to avoid making the type theory inconsistent.  In particular, we cannot lower the level of a type unless it was previously lifted to a (higher than necessary) universe level.

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
We will also need to know that lift and lower compose to the identity.
\begin{code}
lower∼lift : {𝓧 𝓦 : Universe}{X : 𝓧 ̇} → lower{𝓧}{𝓦} ∘ lift ≡ 𝑖𝑑 X
lower∼lift = 𝓻ℯ𝓯𝓵

lift∼lower : {𝓧 𝓦 : Universe}{X : 𝓧 ̇} → lift ∘ lower ≡ 𝑖𝑑 (Lift{𝓧}{𝓦} X)
lift∼lower = 𝓻ℯ𝓯𝓵
\end{code}

Now, getting more "domain-specific," we show how to lift algebraic operation types and then, finally, algebra types themselves.
\begin{code}
module _ {𝑆 : Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇)} where

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

Finally,  we will we want to make the blanket assumption throughout the library that we always have an arbitrary large collection `X` of variable symbols and, no matter in what type the domain of our algebra lies, we can always find a surjective map h₀ : X → ∣ 𝑨 ∣ from our arbitrary collection of variables onto the domain of 𝑨.
    Here is the type we use when making this assumption. -}
\begin{code}
 _↠_ : {𝓤 𝓧 : Universe} → 𝓧 ̇ → Algebra 𝓤 𝑆 → 𝓧 ⊔ 𝓤 ̇
 X ↠ 𝑨 = Σ h ꞉ (X → ∣ 𝑨 ∣) , Epic h
\end{code}
