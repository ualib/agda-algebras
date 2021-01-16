---
layout: default
title : UALib.Prelude.Preliminaries module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

<!--
FILE: Preliminaries.lagda
AUTHOR: William DeMeo
DATE: 14 Jan 2021
REF: Parts of this file are based on the HoTT/UF course notes by Martin Hötzel Escardo (MHE).
SEE: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
     Below, MHE = Martin Hötzel Escardo.
-->

### <a id="preliminaries">Preliminaries</a>

This section describes the [UALib.Prelude.Preliminaries][] module of the [Agda Universal Algebra Library][].

**Notation**. Here are some acronyms that we use frequently.

  * MHE = [Martin Hötzel Escardo](https://www.cs.bham.ac.uk/~mhe/)
  * MLTT = [Martin-Löf Type Theory](https://ncatlab.org/nlab/show/Martin-L%C3%B6f+dependent+type+theory)


#### Options


All Agda programs begin by setting some options, which effect how Agda behaves, and by importing from existing libraries (in our case, the [Agda Standard Library][] and the [Type Topology][] library by MHE). In particular, logical axioms and deduction rules can be specified according to what one wishes to assume.

For example, we start each Agda source file in the library with the following line:

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}

This specifies the Agda `OPTIONS` that we will use throughout the library.

  * `without-K` disables [Streicher's K axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) ; see also the [section on axiom K](https://agda.readthedocs.io/en/v2.6.1/language/without-k.html) in the [Agda Language Reference][] manual.

  * `exact-split` makes Agda accept only those definitions that behave like so-called *judgmental* or *definitional* equalities.  MHE explains this by saying it "makes sure that pattern matching corresponds to Martin-Löf eliminators;" see also the [Pattern matching and equality section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality) of the [Agda Tools][] documentation.

  * `safe` ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module); see also [this section](https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe) of the [Agda Tools][] documentation and the [Safe Agda section](https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda) of the [Agda Language Reference][].

Note that if we wish to type-check a file that imports another file that still has some unmet proof obligations, we must remove the `--safe` flag and insert the `--allow-unsolved-metas` flag, so we could use the following in such case:

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}
```

#### Modules

The `OPTIONS` line is usually followed by the start of a module.  For example, here's how we start the Preliminaries module here.

\begin{code}

module UALib.Prelude.Preliminaries where

\end{code}

Sometimes we may wish to pass in some parameters that will be assumed throughout the module.  For instance, when working with algebras, we often consider algebras of a particular fixed signature, and this is something we could fix as a parameter.  We'll see some examples soon enough, but as a preview,

```agda
module _ {𝑆 : Signature 𝓞 𝓥} where
```

is how we often start an (anonymous) module in which the fixed signature 𝑆 will be assumed until the end of the module. (The module started with the line above would be anonymous because the underscore `_` appears instead of a module name.)

Agda determines where a model begins and ends by indentation.  This can take some getting used to, but after a short time it will seem quite natural.

The main module of a file must have the same name as the file (without the trailing `.agda` or `.lagda`, of course).  The code inside the main module is not indented. Modules may be declared inside the main module and code inside these submodules must be indented to the same column.  As long as the code is indented, Agda considers it part of the submodule.  To exit the submodule, we return to nonindented code.  So, the general pattern is as follows:

```agda

module main where

a-function-in-the-main-module : {𝓤 : Universe}{A B : 𝓤 ̇} → A → B
a-function-in-the-main-module = λ a → a

module _ {𝓤 : Universe} where

 a-function-inside-an-anonymous-submodule : {A B : 𝓤 ̇} → A → B
 a-function-inside-an-anonymous-submodule = λ a → a

a-function-outside-the-submodule : {A B : 𝓤 ̇} → A → B
a-function-outside-the-submodule a = a
```

Actually, for illustration purposes, we have here an example that Agda wouldn't normally accept.  The problem is that the last function above is outside the submodule in which the variable 𝓤 is declared to have type `Universe`.  Therefore, Agda would complain that 𝓤 is not in scope.

In the UAlib, however, we tend to avoid such scope problems by declaring frequently used variable names, like 𝓤, 𝓥, 𝓦, etc., in advance so they are always in scope.  This is done as follows.

\begin{code}
-- open import universes public

-- variable
--   𝓘 𝓙 𝓚 𝓛 𝓜 𝓝 𝓠 𝓡 𝓢 𝓧 : Universe
\end{code}

#### Imports from Type Topology

Throughout we use many of the nice tools that Martin Escardo has developed and made available in his [Type Topology][] repository of Agda code for Univalent Foundations.

We import these now.

\begin{code}
open import universes public

open import Identity-Type renaming (_≡_ to infix 0 _≡_ ; refl to 𝓇ℯ𝒻𝓁) public

pattern refl x = 𝓇ℯ𝒻𝓁 {x = x}

open import Sigma-Type renaming (_,_ to infixr 50 _,_) public

open import MGS-MLTT using (_∘_; domain; codomain; transport; _≡⟨_⟩_; _∎; pr₁; pr₂; -Σ; -- 𝕁;
 Π; ¬; _×_; 𝑖𝑑; _∼_; _+_; 𝟘; 𝟙; 𝟚; _⇔_; lr-implication; rl-implication; id; _⁻¹; ap) public

open import MGS-Equivalences using (is-equiv; inverse; invertible) public

open import MGS-Subsingleton-Theorems using (funext; global-hfunext; dfunext; is-singleton;
 is-subsingleton; is-prop; Univalence; global-dfunext; univalence-gives-global-dfunext; _●_;
 _≃_; logically-equivalent-subsingletons-are-equivalent; Π-is-subsingleton; Σ-is-subsingleton) public

open import MGS-Powerset renaming (_∈_ to _∈₀_; _⊆_ to _⊆₀_; ∈-is-subsingleton to ∈₀-is-subsingleton)
 using (𝓟; equiv-to-subsingleton; powersets-are-sets'; subset-extensionality'; propext; _holds; Ω) public

open import MGS-Embeddings using (Nat; NatΠ; NatΠ-is-embedding; is-embedding; pr₁-embedding; ∘-embedding;
 is-set; _↪_; embedding-gives-ap-is-equiv; embeddings-are-lc; ×-is-subsingleton; id-is-embedding) public

open import MGS-Solved-Exercises using (to-subtype-≡) public

open import MGS-Unique-Existence using (∃!; -∃!) public

open import MGS-Subsingleton-Truncation using (_∙_; to-Σ-≡; equivs-are-embeddings;
 invertibles-are-equivs; fiber; ⊆-refl-consequence; hfunext) public
\end{code}

Notice that we have carefully specified which definitions and results we want to import from each of Escardo's modules.  This is not absolutely necessary, and we could have simply used, e.g., `open import MGS-MLTT public`, omitting the `using (_∘_; domain; ...; ap)`.  However, being specific here has advantages.  Besides helping us avoid naming conflicts, it makes clear exactly which parts of the Martin Escardo (and Martin-Löf!) type theory we are using.

To conclude this preliminary model, we define some syntactic sugar for the first and second projections of a pair.

\begin{code}
module _ {𝓤 : Universe} where
 ∣_∣ fst : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇} → Σ Y → X
 ∣ x , y ∣ = x
 fst (x , y) = x

 ∥_∥ snd : {X : 𝓤 ̇ }{Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
 ∥ x , y ∥ = y
 snd (x , y) = y
\end{code}

Both of these alternative notations,

```agda
fst (x , y) ≡ x, snd(x , y) ≡ y
```

and

```agda
∣ (x , y) ∣ = x, ∥ (x , y) ∥ = y
```

will be used frequently throughout the library.

-------------------------------------

[↑ UALib.Prelude](UALib.Prelude.html)
<span style="float:right;">[UALib.Prelude.Equality →](UALib.Prelude.Equality.html)</span>


{% include UALib.Links.md %}

