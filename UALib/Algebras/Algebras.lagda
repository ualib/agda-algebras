---
layout: default
title : UALib.Algebras.Algebras module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="algebra-types">Algebra Types</a>

This section presents the [UALib.Algebras.Algebras] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Algebras.Algebras where

open import UALib.Algebras.Signatures public

open import UALib.Prelude.Preliminaries using (𝓤₀; 𝟘; 𝟚) public

\end{code}

#### Sets (0-groupoids)

Before defining the type of algebras, we need to explain what it means to be a set in univalent mathematics.  A type is defined to be a **set** if there is at most one way for any two of its elements to be equal.

MHE defines this notion (e.g., in the MGS-Embeddings module) as follows:

```agda
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
```

and explains, "at this point, with the definition of these notions, we are entering the realm of univalent mathematics, but not yet needing the univalence axiom."

#### The main Algebra type

The first type for representing algebras that we define will put the domain of an algebra in an arbitrary type.  We will call these "∞-algebras" because the universe need not be a set.  After that, we define the type of algebra that we typically think of when doing informal universal algebra, which we call "0-algebras" since their domains are sets.

\begin{code}

∞-algebra Algebra : (𝓤 : Universe)(𝑆 : Signature 𝓞 𝓥) →  𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺ ̇

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

#### Algebras as record types

Sometimes records are more convenient than sigma types. For such cases, we might prefer the following representation of the type of algebras.

\begin{code}

module _ {𝓞 𝓥 : Universe} where
 record algebra (𝓤 : Universe) (𝑆 : Signature 𝓞 𝓥) : (𝓞 ⊔ 𝓥 ⊔ 𝓤) ⁺ ̇ where
  constructor mkalg
  field
   univ : 𝓤 ̇
   op : (f : ∣ 𝑆 ∣) → ((∥ 𝑆 ∥ f) → univ) → univ


\end{code}

(Recall, the type `Signature 𝓞 𝓥` is simply defined as the dependent pair type `Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)`.)

Of course, we can go back and forth between the two representations of algebras, like so.

\begin{code}

module _ {𝓤 𝓞 𝓥 : Universe} {𝑆 : Signature 𝓞 𝓥} where

 open algebra

 algebra→Algebra : algebra 𝓤 𝑆 → Algebra 𝓤 𝑆
 algebra→Algebra 𝑨 = (univ 𝑨 , op 𝑨)

 Algebra→algebra : Algebra 𝓤 𝑆 → algebra 𝓤 𝑆
 Algebra→algebra 𝑨 = mkalg ∣ 𝑨 ∣ ∥ 𝑨 ∥

\end{code}

#### Operation interpretation syntax

We conclude this module by defining a convenient shorthand for the interpretation of an operation symbol that we will use often.  It looks more similar to the standard notation one finds in the literature as compared to the double bar notation we started with.

\begin{code}

 _̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra 𝓤 𝑆) → (∥ 𝑆 ∥ f  →  ∣ 𝑨 ∣) → ∣ 𝑨 ∣

 f ̂ 𝑨 = λ x → (∥ 𝑨 ∥ f) x

\end{code}

-------------------------------------

[Back to Table of Contents ↑](UALib.html#detailed-contents)

-------------------------------

{% include UALib.Links.md %}
