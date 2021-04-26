---
layout: default
title : Overture.Lifts module (Agda Universal Algebra Library)
date : 2021-02-18
author: William DeMeo
---

### <a id="agdas-universe-hierarchy">Agda's Universe Hierarchy</a>

This is the [Overture.Lifts][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Overture.Lifts where

open import Overture.Inverses public

\end{code}

#### <a id="agdas-universe-hierarchy">Agda's universe hierarchy</a>

The hierarchy of universes in Agda is structured as follows:<sup>[1](Overture.Lifts.html#fn1)</sup>

```agda
Type 𝓤 : Type (lsuc 𝓤),   Type(lsuc 𝓤) : Type (lsuc (lsuc 𝓤)),  etc.
```

This means that the universe `Type 𝓤` has type `Type(lsuc 𝓤)`, and  `Type(lsuc 𝓤)` has type `Type(lsuc (lsuc 𝓤))`, and so on.  It is important to note, however, this does *not* imply that  `Type 𝓤 : Type(lsuc(lsuc 𝓤))`. In other words, Agda's universe hierarchy is *non-cumulative*. This makes it possible to treat universe levels more precisely, which is nice. On the other hand, a non-cumulative hierarchy can sometimes make for a non-fun proof assistant. Specifically, in certain situations, the non-cumulativity makes it unduly difficult to convince Agda that a program or proof is correct.




#### <a id="lifting-and-lowering">Lifting and lowering</a>

Here we describe a general `Lift` type that help us overcome the technical issue described in the previous subsection.  In the [Lifts of algebras section](Algebras.Algebras.html#lifts-of-algebras) of the [Algebras.Algebras][] module we will define a couple domain-specific lifting types which have certain properties that make them useful for resolving universe level problems when working with algebra types.

Let us be more concrete about what is at issue here by considering a typical example. Agda will often complain with errors like the following:

<samp>
Birkhoff.lagda:498,20-23 <br>
𝓤 != 𝓞 ⊔ 𝓥 ⊔ (lsuc 𝓤) when checking that the expression... has type...
</samp>

This error message means that Agda encountered the universe level `lsuc 𝓤`, on line 498 (columns 20--23) of the file `Birkhoff.lagda`, but was expecting a type at level `𝓞 ⊔ 𝓥 ⊔ lsuc 𝓤` instead.

The general `Lift` record type that we now describe makes these situations easier to deal with. It takes a type inhabiting some universe and embeds it into a higher universe and, apart from syntax and notation, it is equivalent to the `Lift` type one finds in the `Level` module of the [Agda Standard Library][].

\begin{code}

module hide-lift where

 record Lift {𝓦 𝓤 : Level} (A : Type 𝓤) : Type (𝓤 ⊔ 𝓦) where
  constructor lift
  field lower : A

open import Level public

\end{code}

The point of having a ramified hierarchy of universes is to avoid Russell's paradox, and this would be subverted if we were to lower the universe of a type that wasn't previously lifted.  However, we can prove that if an application of `lower` is immediately followed by an application of `lift`, then the result is the identity transformation. Similarly, `lift` followed by `lower` is the identity.

\begin{code}

lift∼lower : ∀ {𝓤 𝓦}{A : Type 𝓤} → lift ∘ lower ≡ 𝑖𝑑 (Lift 𝓦 A)
lift∼lower = refl

lower∼lift : {𝓤 𝓦 : Level}{A : Type 𝓤} → lower {𝓤}{𝓦}(lift {𝓤}{𝓦}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

\end{code}

The proofs are trivial. Nonetheless, we'll come across some holes these lemmas can fill.

---------------

<sup>1</sup><span class="footnote" id="fn1">Recall, from the [Overture.Preliminaries][] module, the special notation we use to denote Agda's *levels* and *universes*.</span>


<p></p>

[← Overture.Inverses](Overture.Inverses.html)
<span style="float:right;">[Relations →](Relations.html)</span>

{% include UALib.Links.md %}