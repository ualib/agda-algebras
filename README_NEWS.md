## 20 Dec 2025: A category-theory refactor of `agda-algebras`

Instead of rewriting everything at once, we will add a *parallel* layer that:

1.  **Recasts signatures as functors / containers**

    +  Our "operation signature" (symbols + arities) is essentially a **polynomial functor** (aka a container) in Set:

       + shapes = operation symbols
       + positions = arity (dependent positions for many-sorted algebras)
       + extension = `⟦Σ⟧ X = Σ (op : Ops) (Pos op → X)` (or its dependent/many-sorted version)

    +  Then an algebra is just an **Eilenberg–Moore algebra** for that endofunctor: `α : ⟦Σ⟧ A → A`.

2.  **Adds algebraic theories / equations as a second layer**

    +  Once we've got terms as the **free monad** on the signature functor, equations
       are a congruence relation on terms.
    +  Models/varieties become "algebras satisfying equations" (or algebras for a quotient monad, depending on how quotienty we want to get).

3.  **Keeps our existing UA-facing API intact**

    +  Our current development has lots of "downstream" lemmas and proofs.
    +  The cats layer can provide *views* (equivalences) so we can say: "this is the same notion, but in functor language."

That path gives us something immediately valuable; we can write docs like:

> "A single-sorted signature is a container (polynomial functor). An algebra is an algebra for that functor. Terms are the free monad. Equations present a theory."

...and keep the old code working while we slowly migrate the pieces we want.

### What we'll learn and what wiil likely be most fun

+  **Polynomial functors / containers**: the sweet spot of "cats flavor" with concrete computations in Agda.
+  **Free monads / substitution**: terms-as-syntax falls out cleanly.
+  **Algebraic theories**: finitary monads, Lawvere theories, presentations.
+  **Initiality / induction principles** become categorical statements we prove once and reuse.

### A minimal "first milestone" that would pay off fast

A very contained first deliverable could be:

+  A module `UA.Signature.Polynomial` that defines:

   +  `Signature : Type` (container-ish)
   +  interpretation `⟦_⟧ : Signature → (Type → Type)`
   +  `Alg : Signature → Type` defined as `Σ A , (⟦Σ⟧ A → A)`
   +  equivalence to your existing notion of an algebra over a signature (where applicable)

This alone would let us sprinkle in cats language in docs and give cat people a familiar entry point.

