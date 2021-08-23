---
layout: default
title : Structures.Terms.Basic
date : 2021-07-02
author: [agda-algebras development team][]
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Level            using ( Level )
open import Structures.Basic using ( signature )


module Structures.Terms.Basic {𝓞 𝓥 : Level}{𝐹 : signature 𝓞 𝓥} where

open import Agda.Primitive using ( lsuc ; _⊔_ ) renaming ( Set to Type )

open signature

data Term  {χ : Level} (X : Type χ ) : Type (lsuc (𝓞 ⊔ 𝓥 ⊔ χ))  where
 ℊ : X → Term X    -- (ℊ for "generator")
 node : (f : symbol 𝐹)(𝑡 : (arity 𝐹) f → Term X) → Term X

\end{code}

--------------------------------

<br>
<br>

[↑ Structures.Terms](Structures.Terms.html)
<span style="float:right;">[Structures.Terms.Operations →](Structures.Terms.Operations.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
