---
layout: default
title : UALib.Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

------------------------------------------------------------

## [The Agda Universal Algebra Library](UALib.html)

----------------------------------------------------------

[UALib.Algebras ↑](UALib.Algebras.html)

### <a id="operation-and-signature-types">Operation and Signature Types</a>

This section presents the [UALib.Algebras.Signatures][] module of the [Agda Universal Algebra Library][].

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module UALib.Algebras.Signatures where

open import UALib.Prelude.Extensionality public

module _ {𝓤 𝓥 : Universe} where
 --The type of operations
 Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 Op I A = (I → A) → A

 --Example. the projections
 π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
 π i x = x i

-- module _
--  {𝓞  -- the universe in which operation symbols live
--   𝓥 -- the universe in which arities live
--   : Universe} where

Signature : (𝓞 𝓥 : Universe) → (𝓞 ⊔ 𝓥) ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇ , ( F → 𝓥 ̇ )
\end{code}

Recall, the definition of the type `Σ`.

```agda
-Σ : {𝓤 𝓥 : Universe}(X : 𝓤 ̇)(Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y
```

-------------------------------------

[Back to Table of Contents ↑](UALib.html#detailed-contents)

------------------------------------------------

{% include UALib.Links.md %}

