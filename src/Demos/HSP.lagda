\section{Introduction}
The \agdaalgebras library \cite{ualib_v2.0.1} formalizes the foundations of universal algebra
in intensional Martin-Löf type theory (\mltt) using \agda~\cite{Norell:2007,agdaref}.
The library includes a wide collection of definitions and verified theorems that faithfully codify
classical, set-theory-based universal algebra and equational
logic.

The first major milestone of the \agdaalgebras project is a proof of \emph{Birkhoff's
variety theorem} (also known as the \emph{HSP theorem})~\cite{Birkhoff:1935}.
To the best of our knowledge, this constitutes the first formal proof of
Birkhoff's in Martin-Löf Type Theory, and it is the first such machine-verified proof of Birkhoff's
celebrated 1935 result.  An alternative formalization, based on classical
set-theory, was achieved in~\cite{birkhoff-in-mizar:1999}; see \href{http://www.mizar.org/JFM/Vol9/birkhoff.html\#BIB21}{mizar.org/JFM/Vol9/birkhoff.html}.

Presented here is our second proof of the HSP theorem. The first proof\footnote{See the
 \href{https://github.com/ualib/ualib.github.io/blob/71f173858701398d56224dd79d152c380c0c2b5e/src/lagda/UALib/Birkhoff.lagda}{\textsf{Birkhoff.lagda}} file
 in the \href{https://github.com/ualib/ualib.github.io}{\textsf{ualib/ualib.gitlab.io}}
 repository (\href{https://github.com/ualib/ualib.github.io/commit/71f173858701398d56224dd79d152c380c0c2b5e}{15
 Jan 2021 commit 71f1738})~\cite{ualib_v1.0.0}.}
suffered from flaws that raised two concerns. First, it was not clear whether the
proof was fully constructive (because of its use of function extensionality in \mltt). Second,
it was shown that if one were to take the type
\ab{X}---which we use to represent an arbitrary collection of
variable symbols---to be  the two element type, then one could combine this with our
proof and derive a contradiction. To resolve these issues, we have rewritten parts of the library and
developed a new proof of the HSP theorem. We are confident that the
proof presented here\footnote{based on \agdaalgebras, ver.~2.0.1~\cite{ualib_v2.0.1}, \agda ver.2.6.2 and \agdastdlib ver.1.7.} is constructive and
 correct. %, a conviction we justify in the sequel (\qv).

What follows is a self-contained formal proof of the HSP theorem in \agda.  This is achieved by
extracting a subset of the \agdaalgebras library, including only the
pieces needed for the proof, into a literate \agda document.\footnote{See
\HSPlagda in the \agdaalgebras repository: \agdaalgebrasrepo .}
\ifshort
For spaces reasons, we elide some inessential parts,
but strive to preserve the essential content and character of the development.
More specifically, routine or overly technical components, as well as anything that does not
seem to offer insight into the central ideas of the proof are omitted.\footnote{The full proof
appears in the unabridged version of the present paper~\cite{DeMeo:2021}.}
\else
We include here every line of code of our new proof of Birkhoff's theorem
in a single \agda module, presented as a literate \agda document,\footnote{See
\HSPlagda in the \agdaalgebras repository: \agdaalgebrasrepo .}.  Apart from a few dozen
imports from the \agdastdlib, the module is self-contained.
\fi

We highlight some of the challenging aspects of formalizing universal algebra in type theory.
Nonetheless, we hope to show that the patient mathematician, with enough resolve and the will to learn
dependent type theory, can reap the rewards of the further insights that mechanization provides.

\ifshort\else
We give a sobering glimpse of the technical hurdles that must be overcome
to conduct research in mathematics using dependent type theory in \agda.
The results are rather gratifying and enlightening, and we feel are worth
the investment. Users of Coq and Lean have recently reported similar feelings
from the outcome of their formalization efforts.
\fi

Our main contribution is the representation of algebraic structures and their signatures
in dependent type theory in a way that is not only very general, but also practical, as we
demonstrate by formalizing one of the deepest results in the field.

\section{Preliminaries}

For the most part, we assume that the reader is familiar with \mltt, and can decipher its encoding in \agda.

\subsection{Logical foundations}

To best emulate \mltt, we use
\begin{code}[inline]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
; these options affect the logical foundations with respect to which our code is type-checked.
\ifshort
Briefly,
\AgdaPragma{without-K} disables
\href{https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29}{Streicher's K axiom},
\AgdaPragma{exact-split} directs \agda to accept only definitions behaving like
{\it judgmental} equalities, and
\AgdaPragma{safe} ensures that nothing is postulated outright.
See~\cite{agdaref-axiomk,agdaref-safeagda,agdatools-patternmatching} for more details.
\else
Here are brief descriptions of these options, accompanied by links to related documentation.
\begin{itemize}
\item
\AgdaPragma{without-K} disables \href{https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29}{Streicher's K axiom}.
See the \href{https://agda.readthedocs.io/en/v2.6.1/language/without-k.html}{section on axiom K} in
the \href{https://agda.readthedocs.io/en/v2.6.1.3/language}{Agda Language Reference Manual}~\cite{agdaref-axiomk}.
\item
\AgdaPragma{exact-split} makes \agda accept only those definitions that behave like so-called {\it judgmental} equalities.
See the \href{https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality}%
{Pattern matching and equality} section of
the \href{https://agda.readthedocs.io/en/v2.6.1.3/tools/}{Agda Tools} documentation~\cite{agdatools-patternmatching}.
\item
\AgdaPragma{safe} ensures that nothing is postulated outright---every non-\mltt axiom has to be an explicit assumption (e.g., an argument to a function or module).
See the \href{https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe}{cmdoption-safe} section of~\cite{agdaref-safeagda}.
\end{itemize}
\fi

We also make use of a variety of definitions from Agda's standard library; these are imported as follows.
\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
\ifshort\else
\begin{code}

-- Import universe levels and Signature type (described below) from the agda-algebras library.
open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where
\end{code}
\fi
\begin{code}

-- Import 16 definitions from the Agda Standard Library.
open import  Data.Unit.Polymorphic                           using ( ⊤ ; tt                        )
open import  Function                                        using ( id ; flip ; _∘_               )
open import  Level                                           using ( Level                         )
open import  Relation.Binary                                 using ( Rel ; Setoid ; IsEquivalence  )
open import  Relation.Binary.Definitions                     using ( Reflexive ; Symmetric         )
                                                             using ( Transitive ; Sym ; Trans      )
open import  Relation.Binary.PropositionalEquality           using ( _≡_                           )
open import  Relation.Unary                                  using ( Pred ; _⊆_ ; _∈_              )

-- Import 23 definitions from the Agda Standard Library and rename 12 of them.
open import  Agda.Primitive  renaming ( Set    to Type    )  using ( _⊔_ ; lsuc                    )
open import  Data.Product    renaming ( proj₁  to fst     )
                             renaming ( proj₂  to snd     )  using ( _×_ ; _,_ ; Σ ; Σ-syntax      )
open import  Function        renaming ( Func   to _⟶_     )  using ( Injection ; Surjection        )
open         _⟶_             renaming ( f      to _⟨$⟩_   )  using ( cong                          )
open         Setoid          renaming ( refl   to reflˢ   )
                             renaming ( sym    to symˢ    )
                             renaming ( trans  to transˢ  )
                             renaming ( _≈_    to _≈ˢ_    )  using ( Carrier ; isEquivalence       )
open         IsEquivalence   renaming ( refl   to reflᵉ   )
                             renaming ( sym    to symᵉ    )
                             renaming ( trans  to transᵉ  )  using ()

\end{code}
\ifshort\else
\begin{code}
-- Assign handles to 3 modules of the Agda Standard Library.
import       Function.Definitions                   as FD
import       Relation.Binary.PropositionalEquality  as ≡
import       Relation.Binary.Reasoning.Setoid       as SetoidReasoning

private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
 𝑓 : fst 𝑆

\end{code}
\fi
The above imports include some adjustments to ``standard \agda'' syntax; in particular,
we use \AgdaPrimitive{Type} in place of \AgdaPrimitive{Set}, the infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, instead of \AgdaRecord{Func} (the type of ``setoid functions,'' discussed in §\ref{setoid-functions} below), and the symbol \aofld{\au{}⟨\$⟩\au{}} in place of \afld{f} (application of the map of a setoid function); we use
\AgdaField{fst} and \AgdaField{snd}, and sometimes \AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}}, to denote the first and second
projections out of the product type
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}.
\ifshort\else

\begin{code}
module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}
\fi

%% -----------------------------------------------------------------------------
\subsection{Setoids}\label{setoids}
A \defn{setoid} is a pair consisting of a type \ab A and
an equivalence relation \af{≈} on \ab A.  Setoids are useful for representing a
set with a ``local'' notion of equivalence, instead of always relying on
the global one as is usually done in set theory. In reality, informal
mathematial practice uses equivalence relations quite pervasively, and
takes great care to only define equivalence-preserving functions, while
eliding the actual details. To be fully formal, such details must be given.
While there are many different approaches for doing that, the one that requires
no additional meta-theory is based on setoids, which is why we adopt it here.
While in some settings this has been found by others to be burdensome, we have not
found it to be so for universal algebra.

\ddmmyydate

The \agdaalgebras library was first developed without setoids, relying on
propositional equality \ad{\au{}≡\au{}} instead,
along with some experimental, domain-specific types for equivalence classes, quotients, etc.
This furthermore required postulating function extensionality,%
\footnote{An axiom that asserts that two point-wise equal functions are equal.} which is
known to be independent from \mltt~\cite{MHE, MHE:2019}. This was
an unsatisfactory state of affairs, as %we were curious to see if
our aim is to show that the theorems hold directly in \mltt without extra axioms.
In particular, the present exposition makes no appeals to classical axioms like Choice or Excluded Middle.


%% -----------------------------------------------------------------------------
\subsection{Setoid functions}
\label{setoid-functions}
We use the \ar{Func} type from the \agdastdlib for representing a function from
a setoid \ab A to another setoid \ab B that respects the underlying equivalences,
witnessed by a field called \afld{cong}.  However, we rename \ar{Func}, using
the more visually appealing infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, instead. Throughout the
paper we refer to inhabitants of this type as ``setoid functions.''

\ifshort\else
An example of a setoid function is the identity function from a setoid to itself.
We define it, along with a binary composition operation for setoid functions,
\AgdaOperator{\AgdaFunction{⟨∘⟩}}, as follows.

\begin{code}

𝑖𝑑 : {A : Setoid α ρᵃ} → A ⟶ A
𝑖𝑑 {A} = record { f = id ; cong = id }

_⟨∘⟩_ :  {A : Setoid α ρᵃ} {B : Setoid β ρᵇ} {C : Setoid γ ρᶜ}
 →       B ⟶ C  →  A ⟶ B  →  A ⟶ C

f ⟨∘⟩ g = record  { f = (_⟨$⟩_ f) ∘ (_⟨$⟩_ g)
                  ; cong = (cong f) ∘ (cong g) }
\end{code}
\fi

\paragraph*{Inverses}
We frequently need to deal with the \defn{inverse} of a function. This is most easily defined in terms of the
\emph{image} of the function's domain, as follows.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b

\end{code}

An inhabitant of the \aod{Image} \ab f \aod{∋} \ab b type is a point \ab a of type \ab A,
along with a proof, \ab p~\as :~\ab b \af{≈} \ab f~\ab a, that \ab f maps \ab a to \ab b.
Since the witness that \ab b
belongs to the image of \ab f is always accompanied by a concrete witness \AgdaTyped{a}{A}, we can
\emph{compute} a range-restricted right-inverse of \ab f.  For extra certainty, we also verify
that our witness really is an inverse.

\begin{code}

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p
\end{code}

\paragraph*{Injective and surjective setoid functions}
If \ab{f} : \ab{𝑨} \aor{⟶} \ab{𝑩}
then we call \ab f \defn{injective} provided
\as{∀} (\ab{a₀} \ab{a₁} \as : \ab{A}), \ab{f} \aofld{⟨\$⟩} \ab{a₀} \af{≈ᴮ} \ab{f} \aofld{⟨\$⟩} \ab{a₁}
implies \ab{a₀} \af{≈ᴬ} \ab{a₁}; we call \ab{f} \defn{surjective} provided
\as{∀} (\AgdaTyped{b}{B}), \as{∃}~(\AgdaTyped{a}{A}) such that \ab{f} \aofld{⟨\$⟩} \ab{a} \af{≈ᴮ} \ab{b}.
\ifshort
We omit the straightforward \agda definitions.
\else

We represent injective functions on bare types by the
type \af{Injective}, and uses this to define the \af{IsInjective} type to represent
the property of being an injective setoid function. Similarly, the type \af{IsSurjective}
represents the property of being a surjective setoid function. \af{SurjInv} represents the \emph{right-inverse} of a surjective function.

We reproduce the definitions and prove some of their properties
inside the next submodule where we first set the stage by declaring two
setoids \ab{𝑨} and \ab{𝑩}, naming their equality relations, and making some
definitions from the standard library available.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈ᴮ_ )
 open FD _≈ᴬ_ _≈ᴮ_

 IsInjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ ρᵃ ⊔ ρᵇ)
 IsInjective f = Injective (_⟨$⟩_ f)

 IsSurjective : (𝑨 ⟶ 𝑩) →  Type (α ⊔ β ⊔ ρᵇ)
 IsSurjective F = ∀ {y} → Image F ∋ y

 SurjInv : (f : 𝑨 ⟶ 𝑩) → IsSurjective f → Carrier 𝑩 → Carrier 𝑨
 SurjInv f fonto b = Inv f (fonto {b})

\end{code}

Proving that the composition of injective setoid functions is again injective
is simply a matter of composing the two assumed witnesses to injectivity.
Proving that surjectivity is preserved under composition is only slightly more involved.

\begin{code}

module _  {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ}{𝑪 : Setoid γ ρᶜ}
          (f : 𝑨 ⟶ 𝑩)(g : 𝑩 ⟶ 𝑪) where

 ∘-IsInjective : IsInjective f → IsInjective g → IsInjective (g ⟨∘⟩ f)
 ∘-IsInjective finj ginj = finj ∘ ginj

 ∘-IsSurjective : IsSurjective f → IsSurjective g → IsSurjective (g ⟨∘⟩ f)
 ∘-IsSurjective fonto gonto {y} = Goal
  where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto
   where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto
\end{code}
\fi

\paragraph*{Kernels of setoid functions}
The \defn{kernel} of a function \ab f~\as :~\ab A~\as{→}~\ab B (where \ab A and \ab B are
bare types) is defined informally by \{\AgdaPair{x}{y} \aod{∈} \ab A \aof{×} \ab A \as :
\ab f \ab x \as{=} \ab f \ab y \}. This can be represented in \agda in a number of ways,
but for our purposes it is convenient to define the kernel as an inhabitant of a (unary)
predicate over \ab A \aof{×} \ab A, where \ab A is the function's domain, as follows.

\begin{code}

kernel : {A : Type α}{B : Type β} → Rel B ρ → (A → B) → Pred (A × A) ρ
kernel _≈_ f (x , y) = f x ≈ f y

\end{code}
The kernel of a \emph{setoid} function \ab f \as : \ab{𝐴} \aor{⟶} \ab{𝐵} is
defined similarly.

\ifshort\else
\begin{code}
module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴 using () renaming ( Carrier to A )
\end{code}
\fi
\begin{code}

 ker : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 ker g (x , y) = g ⟨$⟩ x ≈ g ⟨$⟩ y where open Setoid 𝐵 using ( _≈_ )
\end{code}


%% -------------------------------------------------------------------------------------

\section{Basic Universal Algebra}
\label{basic-universal-algebra}
We now develop a working vocabulary in \mltt corresponding to classical,
single-sorted, set-based universal algebra.
We cover a number of important concepts, but limit ourselves to those
required to prove Birkhoff's HSP theorem.
In each case, we give a type-theoretic version of the informal definition,
followed by an \agda implementation.

This section is organized into the following subsections:
§\ref{signatures} defines a general notion of \emph{signature} of a structure and
then defines a type that represent signatures;
§\ref{algebras} does the same for \emph{algebraic structures} and \emph{product algebras};
§\ref{homomorphisms} defines \emph{homomorphisms}, \emph{monomorphisms}, and \emph{epimorphisms},
presents types that codify these concepts, and formally verifies some of their basic properties;
§§\ref{subalgebras}--\ref{terms} do the same for \emph{subalgebras} and \emph{terms}, respectively.

%% -----------------------------------------------------------------------------
\subsection{Signatures}
\label{signatures}

\ifshort
An (algebraic) \defn{signature}
\else
In model theory, the \defn{signature} of a structure is a quadruple \ab{𝑆} = (\ab{C},
\ab{F}, \ab{R}, \ab{ρ}) consisting of three (possibly empty) sets \ab{C}, \ab{F}, and
\ab{R}---called \emph{constant}, \emph{function}, and \emph{relation} symbols,
respectively---along with a function \ab{ρ} : \ab{C} \as{+} \ab{F} \as{+} \ab{R}
\as{→} \ab{N} that assigns an \emph{arity} to each symbol. Often, but not always, \ab{N}
is taken to be the set of natural numbers.

As our focus here is universal algebra, we consider the restricted notion of an
\emph{algebraic signature}, that is, a signature for ``purely algebraic'' structures. Such
a signature
\fi
is a pair \ab{𝑆} = \AgdaPair{F}{ρ} where \ab{F} is a collection of
\defn{operation symbols} and \ab{ρ} : \ab{F} \as{→} \ab{N} is an \defn{arity function}
which maps each operation symbol to its arity. Here, \ab{N} denotes the \emph{arity type}.
Heuristically, the arity \ab{ρ} \ab{f} of an operation symbol \ab{f} \as{∈} \ab{F} may be
thought of as the number of arguments that \ab{f} takes as ``input.''
Here (and in the Agda Universal Algebra Library) we represent signatures in a very general way, as the
inhabitants of the following dependent pair type.

\begin{center}

\AgdaFunction{Signature}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{Level}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaPrimitive{lsuc}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaOperator{\AgdaPrimitive{⊔}}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSymbol{))}\\[4pt]
\AgdaFunction{Signature}\AgdaSpace{}%
\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaFunction{Σ[}\AgdaSpace{}%
\AgdaBound{F}\AgdaSpace{}%
\AgdaFunction{∈}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaFunction{]}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{F}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaPrimitive{Type}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSymbol{)}

\end{center}
Recalling our syntax for the first and second
projections, if \ab{𝑆} %\as{:} \af{Signature} \ab{𝓞} \ab{𝓥}
is a signature, then
\aof{∣} \ab{𝑆} \aof{∣} denotes the set of operation symbols and \aof{∥} \ab{𝑆} \aof{∥} denotes the arity function.
Thus, if \ab{f} \as{:} \aof{∣} \ab{𝑆} \aof{∣} is an operation symbol in the
signature \ab{𝑆}, then \aof{∥} \ab{𝑆} \aof{∥} \ab{f} is the arity of \ab{f}.

We need to augment the \af{Signature} type so that it supports algebras over setoid domains.
\ifshort\else
To do so---following Andreas Abel's lead (cf.~\cite{Abel:2021})---we
define an operator that translates an ordinary signature into a \defn{setoid signature},
that is, a signature over a setoid domain.
\fi
This raises a minor technical issue:
given operations \ab{f} and \ab{g}, with arguments
\ab{u} \as{:} \aof{∥} \ab{𝑆} \aof{∥} \ab{f} \as{→}\ab{A} and \ab{v} \as{:} \aof{∥} \ab{𝑆}
\aof{∥} \ab{g} \as{→} \ab{A}, respectively, and a proof that \ab{f} \aod{≡} \ab{g} (i.e.
intensionally), we ought to be able to check whether \ab u and \ab v are pointwise
equal. Technically, \ab{u} and \ab{v} appear to inhabit different types; this is where the
hypothesis \ab f \aod{≡} \ab g comes in, as we see in the definition of \af{EqArgs} below (adapted
from Andreas Abel's development~\cite{Abel:2021}).

\begin{code}

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)
EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

\end{code}
\noindent
This enables us to define an operator which translates a signature for algebras over bare types into a signature for algebras over setoids.
\ifshort\else
We denote this operator by \aof{⟨\AgdaUnderscore{}⟩} and define it as follows.
\fi

\begin{code}

⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)
\end{code}

%% -----------------------------------------------------------------------------
\subsection{Algebras}\label{algebras}
Informally, an \defn{algebraic structure} \ab{𝑨} = (\ab{A}, \ab{Fᴬ}) \defn{in the signature}
\ab{𝑆} = (\ab{F}, \ab{ρ}), or \ab{𝑆}-\defn{algebra}, consists of
\begin{itemize}
\item a nonempty type \ab A, called the \defn{domain} (or \defn{carrier} or
\defn{universe}) of the algebra;
\item a collection \ab{Fᴬ} :=
  \{ \ab{fᴬ} \as{∣} \ab f \as{∈} \ab F, \ab{fᴬ} \as :
    (\ab{ρ} \ab f \as{→} \ab A) \as{→} \ab A \} of \defn{operations} on \ab{A};
\item a (potentially empty) collection of \defn{identities} satisfied by elements and
operations of \ab{𝑨}.
\end{itemize}
Our \agda implementation represents algebras as inhabitants of a record type with two
fields---a \afld{Domain} setoid denoting the domain of the algebras, and an \afld{Interp} function denoting the interpretation of each operation symbol in \ab{𝑆}. We postpone introducing identities until~§\ref{equational-logic}.

\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain

\end{code}
Thus, for each operation symbol in \ab{𝑆}, we have a setoid function
\ab f, whose domain is a power of \afld{Domain}, and whose codomain is \afld{Domain}.

Further, we define some syntactic sugar to make our formalizations easier to read and comprehend.
Specifically, if \ab{𝑨} is an algebra, then
\begin{itemize}
\item \aof{𝔻[ \ab{𝑨} ]} denotes the \afld{Domain} setoid of \ab{𝑨},
\item \aof{𝕌[ \ab{𝑨} ]} is the underlying carrier of (the \afld{Domain} setoid of) \ab{𝑨}, and
\item \ab f \aof{̂} \ab{𝑨} denotes the interpretation of the operation symbol \ab f in the algebra \ab{𝑨}.
\end{itemize}
\ifshort %%% BEGIN SHORT VERSION ONLY
 We omit the straightforward formal definitions of these types (\seemedium).
\else    %%% END SHORT VERSION ONLY
         %%% BEGIN LONG VERSION ONLY SECTION
\begin{code}
open Algebra
𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨
𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)
_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
\end{code}
\fi

%% -----------------------------------------------------------------------------
\paragraph*{Universe levels of algebra types}
Types belong to \emph{universes}, which are structured in \agda as
follows:
\ap{Type} \ab{ℓ} : \ap{Type} (\ap{suc} \ab{ℓ}), \ap{Type} (\ap{suc} \ab{ℓ}) : \ap{Type}
(\ap{suc} (\ap{suc} \ab{ℓ})), ….\footnote{\ap{suc} \ab{ℓ} denotes the successor of \ab{ℓ} in the universe hierarchy.} While this means that \ap{Type} \ab{ℓ} has type \ap{Type}
(\ap{suc} \ab{ℓ}), it does \emph{not} imply that \ap{Type} \ab{ℓ} has type
\ap{Type} (\ap{suc} (\ap{suc} \ab{ℓ})). In other words, \agda's universes are
\emph{non-cumulative}.
This can be advantageous as it becomes possible to treat size issues
more generally and precisely.  However, dealing with explicit
universe levels can be daunting, and the standard literature
(in which uniform smallness is typically assumed) offers little guidance.
\ifshort\else
This aspect of the language was one of the few stumbling
blocks we encountered while learning how to use \agda for formalizing universal algebra in
type theory. Although some may consider this to be one of the least interesting and most
technical aspects of this paper, others might find the presentation more helpful if we
resist the urge to gloss over these technicalities.
\fi
While in some settings, such as category theory, formalizing it in \agda~\cite{agda-categories}
works smoothly with respect to universe levels, in universal algebra the terrain is bumpier.
Thus, it seems worthwhile to explain how we make use
of universe lifting and lowering functions, available in the \agdastdlib, to
develop domain-specific tools for dealing with \agda's non-cumulative universe hierarchy.

\ifshort\else
Let us be more concrete about what is at issue by considering a typical example. \agda
frequently encounters problems during the type-checking process and responds by printing a
message like the following.
{\color{red}{\small
\begin{verbatim}
  HSP.lagda:498,20-23
  α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that... has type...
\end{verbatim}}}
\noindent Here \agda informs us that it encountered universe level \ab{α} on line 498 of
the HSP module, where it was expecting level \ab{𝓞}~\aop{⊔}~\ab{𝓥}~\aop{⊔}~(\ap{lsuc}
\ab{α}). In this case, we tried to use an algebra inhabiting the type \ar{Algebra}
\ab{α} \ab{ρᵃ} whereas \agda expected an inhabitant of the type \ar{Algebra} (\ab{𝓞}
\aop{⊔} \ab{𝓥} \aop{⊔} (\ap{lsuc} \ab{α})) \ab{ρᵃ}.
\fi
The \ar{Lift} operation of the standard library embeds a type into a higher universe.
Specializing \ar{Lift} to our situation, we
define a function \af{Lift-Alg}%
\ifshort
~with the following interface.
\vskip-2mm
\else
.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans ) ; open Level
 Lift-Algˡ : (ℓ : Level) → Algebra (α ⊔ ℓ) ρᵃ
 Domain (Lift-Algˡ ℓ) =
  record  { Carrier        = Lift ℓ 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → lower x ≈ lower y
          ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }}

 Interp (Lift-Algˡ ℓ) ⟨$⟩ (f , la) = lift ((f ̂ 𝑨) (lower ∘ la))
 cong (Interp (Lift-Algˡ ℓ)) (≡.refl , lab) = cong (Interp 𝑨) ((≡.refl , lab))

 Lift-Algʳ : (ℓ : Level) → Algebra α (ρᵃ ⊔ ℓ)
 Domain (Lift-Algʳ ℓ) =
  record  { Carrier        = 𝕌[ 𝑨 ]
          ; _≈_            = λ x y → Lift ℓ (x ≈ y)
          ; isEquivalence  = record  { refl  = lift refl
                                     ; sym   = lift ∘ sym ∘ lower
                                     ; trans = λ x y → lift (trans (lower x)(lower y)) }}

 Interp (Lift-Algʳ ℓ ) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (Lift-Algʳ ℓ))(≡.refl , lab) = lift(cong(Interp 𝑨)(≡.refl , λ i → lower (lab i)))
\end{code}
\fi

\begin{code}

Lift-Alg : Algebra α ρᵃ → (ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
\end{code}
\ifshort
\vskip2mm
\else
\begin{code}
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁

\end{code}
\fi
\noindent Recall that our \ar{Algebra} type has two universe level parameters, corresponding
to those of the domain setoid.
\ifshort\else
Concretely, an algebra of type \ar{Algebra} \ab{α} \ab{ρᵃ} has a
\afld{Domain} of type \ar{Setoid} \ab{α} \ab{ρᵃ}. This packages a ``carrier set''
(\afld{Carrier}), inhabiting \ap{Type} \ab{α}, with an equality on \afld{Carrier} of type
\af{Rel} \afld{Carrier} \ab{ρᵃ}.
\fi
\af{Lift-Alg} takes an algebra parametrized by levels \ab{a} and \ab{ρᵃ}
and constructs a new algebra whose
carrier inhabits \ap{Type} (\ab{α} \ap{⊔} \ab{ℓ₀}) with equality of type \af{Rel}
\afld{Carrier} (\ab{ρᵃ} \ap{⊔} \ab{ℓ₁}). To be useful, this lifting operation should
result in an algebra with the same semantic properties as the input algebra, which is
indeed the case
\ifshort
(\qv).
\else
as we will see in §\ref{isomorphisms}.
\fi

\paragraph*{Product Algebras}
Recall the (informal) definition of the \defn{product} of a family of
\ab{𝑆}-algebras.
Let \ab{ι} be a universe and \ab I~:~\ap{Type}~\ab{ι} a type (the ``indexing type'').
Then \ab{𝒜}~:~\ab I~\as{→}~\ab{Algebra}~\ab{α}~\ab{ρᵃ} represents
an \defn{indexed family of algebras}.
Denote by \af{⨅}~\ab{𝒜} the \defn{product of algebras} in \ab{𝒜} (or \defn{product
algebra}), by which we mean the algebra whose domain is the Cartesian product \af{Π}~\ab
i~꞉~\ab I~\af{,}~\aof{𝔻[~\ab{𝒜}~\ab i~]} of the domains of the algebras in \ab{𝒜}, and
whose operations are those arising by pointwise interpretation in the obvious way: if
\ab{f} is a \ab J-ary operation symbol and if
\ab a~:~\af{Π}~\ab i~꞉~\ab I~\af{,}~\ab J~\as{→}~\aof{𝔻[~\ab{𝒜}~\ab i~]} is, for each
\ab i~:~\ab I, a \ab J-tuple of elements of the domain \aof{𝔻[~\ab{𝒜}~\ab i~]}, then
we define the interpretation of \ab f in \af{⨅}~\ab{𝒜} by\\[-2mm]

(\ab{f}~\af{̂}~\af{⨅}~\ab{𝒜}) \ab a := \as{λ}~(\ab i~:~\ab I)~\as{→}
(\ab{f}~\af{̂}~\ab{𝒜}~\ab i)(\ab{a}~\ab i).\\[8pt]
Here is how we formalize the concept of product algebra in \agda.

\begin{code}

module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)

 Domain (⨅ 𝒜) =
  record { Carrier = ∀ i → 𝕌[ 𝒜 i ]
         ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
         ; isEquivalence =
            record  { refl   = λ i →      reflᵉ   (isEquivalence 𝔻[ 𝒜 i ])
                    ; sym    = λ x i →    symᵉ    (isEquivalence 𝔻[ 𝒜 i ])(x i)
                    ; trans  = λ x y i →  transᵉ  (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i) }}

 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)

 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong (Interp (𝒜 i)) (≡.refl , flip f=g i )

\end{code}
\noindent Evidently, the \afld{Carrier} of the product algebra type is indeed the (dependent)
product of the carriers in the indexed family. The rest of the definitions are the ``pointwise''
versions of the underlying ones.

%% -------------------------------------------------------------------------------------
\subsection{Homomorphisms}\label{homomorphisms}
Throughout the rest of the paper, unless stated otherwise, \ab{𝑨} and \ab{𝑩}
will denote \ab{𝑆}-algebras inhabiting the types \af{Algebra} \ab{α} \ab{ρᵃ} and
\af{Algebra} \ab{β} \ab{ρᵇ}, respectively.

A \defn{homomorphism} (or ``hom'') from
\ab{𝑨} to \ab{𝑩} is a setoid function \ab{h}~:~\aof{𝔻[~\ab{𝑨}~]} \aor{⟶} \aof{𝔻[~\ab{𝑩}~]}
that is \defn{compatible} with all basic operations; that is, for
every operation symbol \ab{f} : \af{∣~\ab{𝑆}~∣} and all tuples
\ab{a} : \af{∥~\ab{𝑆}~∥}~\ab{f} \as{→} \aof{𝕌[~\ab{𝑨}~]}, we have \ab{h} \aofld{⟨\$⟩}
(\ab{f}~\af{̂}~\ab{𝑨}) \ab{a} \af{≈}
(\ab{f}~\af{̂}~\ab{𝑩}) \ab{h} \aofld{⟨\$⟩} (\ab{a} \au{}).\footnote{Here we use
\ab{h} \aofld{⟨\$⟩} (\ab{a} \au{}) as a shorthand for
\as{λ} \ab x \as{→} \ab h \AgdaOperator{\AgdaField{⟨\$⟩}} (\ab a \ab x).}

It is convenient to first formalize ``compatible'' (\af{compatible-map-op}),
representing the assertion that a given setoid function
\ab{h}~:~\aof{𝔻[~\ab{𝑨}~]} \aor{⟶} \aof{𝔻[~\ab{𝑩}~]} commutes with a given
operation symbol \ab{f}, and then generalize over operation symbols (\af{compatible-map}),
to yield the type of compatible maps from (the domain of) \ab{𝑨} to (the domain of) \ab{𝑩}.

\ifshort\else
\begin{code}

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
\end{code}
\fi
\begin{code}

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f

\end{code}
Using these we define the property (\ar{IsHom}) of being a homomorphism, and
finally the type \af{hom} of homomorphisms from \ab{𝑨} to \ab{𝐵}.

\begin{code}

 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor mkhom ; field compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

\end{code}
Thus, an inhabitant of \af{hom} is a pair (\ab h , \ab p) consisting of
a setoid function \ab h, from the domain of \ab{𝑨} to that of \ab{𝑩}, along with
a proof \ab p that \ab h is a homomorphism.

A \defn{monomorphism} (resp. \defn{epimorphism}) is an injective (resp. surjective)
homomorphism. We define predicates \ar{IsMon} and \ar{IsEpi} for these,
 well as \af{mon} and \af{epi} for the corresponding types.
\ifshort %%% BEGIN SHORT VERSION ONLY
\else    %%% BEGIN LONG VERSION ONLY

\begin{code}

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h

  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

\end{code}
As with \af{hom}, the type \af{mon} is a dependent product type; each inhabitant is a pair
consisting of a setoid function, say, \ab h, along with a proof that \ab h is a
monomorphism.

\begin{code}

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h

  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
\end{code}

Here are two utilities that are useful for translating between types.

\begin{code}
open IsHom ; open IsMon ; open IsEpi

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
\end{code}

\paragraph*{Composition of homomorphisms}
\fi      %%% END LONG VERSION ONLY SECTION
The composition of homomorphisms is again a homomorphism, and similarly for epimorphisms and monomorphisms.
\ifshort
The proofs of these facts are straightforward so we omit them, but give them the names
\af{∘-hom} and \af{∘-epi} so we can refer to them below.
\else

\begin{code}

module _  {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ}
          {g : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]}{h : 𝔻[ 𝑩 ] ⟶ 𝔻[ 𝑪 ]} where

  open Setoid 𝔻[ 𝑪 ] using ( trans )

  ∘-is-hom : IsHom 𝑨 𝑩 g → IsHom 𝑩 𝑪 h → IsHom 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-hom ghom hhom = mkhom c
   where
   c : compatible-map 𝑨 𝑪 (h ⟨∘⟩ g)
   c = trans (cong h (compatible ghom)) (compatible hhom)

  ∘-is-epi : IsEpi 𝑨 𝑩 g → IsEpi 𝑩 𝑪 h → IsEpi 𝑨 𝑪 (h ⟨∘⟩ g)
  ∘-is-epi gE hE = record  { isHom = ∘-is-hom (isHom gE) (isHom hE)
                           ; isSurjective = ∘-IsSurjective g h (isSurjective gE) (isSurjective hE) }

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where

  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ⟨∘⟩ h) , ∘-is-hom hhom ghom

  ∘-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ∘-epi (h , hepi) (g , gepi) = (g ⟨∘⟩ h) , ∘-is-epi hepi gepi
\end{code}

\paragraph*{Universe lifting of homomorphisms}
Here we define the identity homomorphism for setoid algebras. Then we prove that the
operations of lifting and lowering of a setoid algebra are homomorphisms.

\begin{code}

𝒾𝒹 : {𝑨 : Algebra α ρᵃ} → hom 𝑨 𝑨
𝒾𝒹 {𝑨 = 𝑨} = 𝑖𝑑 , mkhom (reflexive ≡.refl) where open Setoid ( Domain 𝑨 ) using ( reflexive )

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 open Setoid 𝔻[ 𝑨 ]              using ( reflexive )  renaming ( _≈_ to _≈₁_ ; refl to refl₁ )
 open Setoid 𝔻[ Lift-Algˡ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ˡ_ ; refl to reflˡ)
 open Setoid 𝔻[ Lift-Algʳ 𝑨 ℓ ]  using ()             renaming ( _≈_ to _≈ʳ_ ; refl to reflʳ)
 open Level

 ToLiftˡ : hom 𝑨 (Lift-Algˡ 𝑨 ℓ)
 ToLiftˡ = record { f = lift ; cong = id } , mkhom (reflexive ≡.refl)

 FromLiftˡ : hom (Lift-Algˡ 𝑨 ℓ) 𝑨
 FromLiftˡ = record { f = lower ; cong = id } , mkhom reflˡ

 ToFromLiftˡ : ∀ b →  ∣ ToLiftˡ ∣ ⟨$⟩ (∣ FromLiftˡ ∣ ⟨$⟩ b) ≈ˡ b
 ToFromLiftˡ b = refl₁

 FromToLiftˡ : ∀ a → ∣ FromLiftˡ ∣ ⟨$⟩ (∣ ToLiftˡ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftˡ a = refl₁

 ToLiftʳ : hom 𝑨 (Lift-Algʳ 𝑨 ℓ)
 ToLiftʳ = record { f = id ; cong = lift } , mkhom (lift (reflexive ≡.refl))

 FromLiftʳ : hom (Lift-Algʳ 𝑨 ℓ) 𝑨
 FromLiftʳ = record { f = id ; cong = lower } , mkhom reflˡ

 ToFromLiftʳ : ∀ b → ∣ ToLiftʳ ∣ ⟨$⟩ (∣ FromLiftʳ ∣ ⟨$⟩ b) ≈ʳ b
 ToFromLiftʳ b = lift refl₁

 FromToLiftʳ : ∀ a → ∣ FromLiftʳ ∣ ⟨$⟩ (∣ ToLiftʳ ∣ ⟨$⟩ a) ≈₁ a
 FromToLiftʳ a = refl₁


module _ {𝑨 : Algebra α ρᵃ}{ℓ r : Level} where
 open  Setoid 𝔻[ 𝑨 ]               using ( refl )
 open  Setoid 𝔻[ Lift-Alg 𝑨 ℓ r ]  using ( _≈_ )
 open  Level

 ToLift : hom 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift = ∘-hom ToLiftˡ ToLiftʳ

 FromLift : hom (Lift-Alg 𝑨 ℓ r) 𝑨
 FromLift = ∘-hom FromLiftʳ FromLiftˡ

 ToFromLift : ∀ b → ∣ ToLift ∣ ⟨$⟩ (∣ FromLift ∣ ⟨$⟩ b) ≈ b
 ToFromLift b = lift refl

 ToLift-epi : epi 𝑨 (Lift-Alg 𝑨 ℓ r)
 ToLift-epi = ∣ ToLift ∣ ,  record { isHom = ∥ ToLift ∥
                            ; isSurjective = λ {y} → eq (∣ FromLift ∣ ⟨$⟩ y) (ToFromLift y) }
\end{code}

\paragraph*{Homomorphisms of product algebras}
Suppose we have an algebra \ab{𝑨}, a type \ab I : \ap{Type} \ab{𝓘}, and a family \ab{ℬ} :
\ab I \as{→} \ar{Algebra} \ab{β} \ab{ρᵇ} of algebras.
We sometimes refer to the inhabitants of \ab{I} as \emph{indices}, and call \ab{ℬ} an
\defn{indexed family of algebras}. If in addition we have a family \ab{𝒽} : (\ab i : \ab
I) → \af{hom} \ab{𝑨} (\ab{ℬ} \ab i) of homomorphisms, then we can construct a homomorphism
from \ab{𝑨} to the product \af{⨅} \ab{ℬ} in the natural way.  We codify the latter in
dependent type theory as follows.

\begin{code}

module _ {ι : Level}{I : Type ι}{𝑨 : Algebra α ρᵃ}(ℬ : I → Algebra β ρᵇ)  where
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom
  where
  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
  h ⟨$⟩ a = λ i → ∣ 𝒽 i ∣ ⟨$⟩ a
  cong h xy i = cong ∣ 𝒽 i ∣ xy
  hhom : IsHom 𝑨 (⨅ ℬ) h
  compatible hhom = λ i → compatible ∥ 𝒽 i ∥
\end{code}

\paragraph*{Factorization of homomorphisms}
\fi      %%% END LONG VERSION ONLY SECTION
We also formalize (as \af{HomFactor}) the following factorization theorem: if \ab g : \af{hom}
\ab{𝑨} \ab{𝑩}, \ab h : \af{hom} \ab{𝑨} \ab{𝑪}, \ab h is surjective, and \af{ker} \ab h
\aof{⊆} \af{ker} \ab g, then there exists \ab{φ} : \af{hom} \ab{𝑪} \ab{𝑩} such that \ab g
= \ab{φ} \aof{∘} \ab h.
\ifshort\else

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ){𝑪 : Algebra γ ρᶜ}
         (gh : hom 𝑨 𝑩)(hh : hom 𝑨 𝑪) where
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ )
 open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈₃_ )
 private gfunc = ∣ gh ∣ ; g = _⟨$⟩_ gfunc ; hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 HomFactor :  kernel _≈₃_ h ⊆ kernel _≈₂_ g
  →           IsSurjective hfunc
  →           Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ a → g a ≈₂ ∣ φ ∣ ⟨$⟩ h a
 HomFactor Khg hE = (φmap , φhom) , gφh
  where
  h⁻¹ : 𝕌[ 𝑪 ] → 𝕌[ 𝑨 ]
  h⁻¹ = SurjInv hfunc hE

  η : ∀ {c} → h (h⁻¹ c) ≈₃ c
  η = InvIsInverseʳ hE

  open Setoid 𝔻[ 𝑪 ] using ( sym ; trans )
  ζ : ∀{x y} → x ≈₃ y → h (h⁻¹ x) ≈₃ h (h⁻¹ y)
  ζ xy = trans η (trans xy (sym η))

  φmap : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
  _⟨$⟩_ φmap = g ∘ h⁻¹
  cong φmap = Khg ∘ ζ

  open _⟶_ φmap using () renaming (cong to φcong)

  gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φmap ⟨$⟩ h a
  gφh a = Khg (sym η)

  φcomp : compatible-map 𝑪 𝑩 φmap
  φcomp {f}{c} =
   begin
    φmap ⟨$⟩  (f ̂ 𝑪)                   c       ≈˘⟨  φcong (cong (Interp 𝑪) (≡.refl , λ _ → η))  ⟩
    g(h⁻¹(    (f ̂ 𝑪)  (h ∘    h⁻¹  ∘  c  )))   ≈˘⟨  φcong (compatible ∥ hh ∥)                   ⟩
    g(h⁻¹(h(  (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))))  ≈˘⟨  gφh ((f ̂ 𝑨)(h⁻¹ ∘ c))                      ⟩
    g(        (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))    ≈⟨   compatible ∥ gh ∥                           ⟩
              (f ̂ 𝑩)  (g ∘ (  h⁻¹  ∘  c  ))    ∎ where open SetoidReasoning 𝔻[ 𝑩 ]

  φhom : IsHom 𝑪 𝑩 φmap
  compatible φhom = φcomp
\end{code}

\subsection{Isomorphisms}
\label{isomorphisms}
\fi      %%% END LONG VERSION ONLY SECTION

Two structures are \defn{isomorphic} provided there are homomorphisms from each to the
other that compose to the identity. We codify this notion, as
well as some of its obvious consequences, as the type \ar{\au{}≅\au{}}.
\ifshort
\else
Note that the definition, shown below, includes a proof of the fact that the maps \afld{to} and
\afld{from} are bijective, which makes this fact more accessible.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ] using () renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᴮ_ )
\end{code}
\fi
\begin{code}

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field        to : hom 𝑨 𝑩
               from : hom 𝑩 𝑨
               to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
               from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ᴬ a
\end{code}
\ifshort
Moreover, \afld{to} and \afld{from} are bijections
and \ar{\au{}≅\au{}} is an equivalence relation (\seemedium).
\else
\begin{code}

  toIsSurjective : IsSurjective ∣ to ∣
  toIsSurjective {y} = eq (∣ from ∣ ⟨$⟩ y) (sym (to∼from y))
   where open Setoid 𝔻[ 𝑩 ] using ( sym )

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x}{y} xy = trans (sym (from∼to x)) (trans ξ (from∼to y))
   where
   open Setoid 𝔻[ 𝑨 ] using ( sym ; trans )
   ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ᴬ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
   ξ = cong ∣ from ∣ xy

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {x} = eq (∣ to ∣ ⟨$⟩ x) (sym (from∼to x))
   where open Setoid 𝔻[ 𝑨 ] using ( sym )

  fromIsInjective : IsInjective ∣ from ∣
  fromIsInjective {x}{y} xy = trans (sym (to∼from x)) (trans ξ (to∼from y))
   where
   open Setoid 𝔻[ 𝑩 ] using ( sym ; trans )
   ξ : ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ x) ≈ᴮ ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ y)
   ξ = cong ∣ to ∣ xy

open _≅_

\end{code}

It is easy to prove that \ar{\au{}≅\au{}} is an equivalence relation, as follows.

\begin{code}

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl where open Setoid 𝔻[ 𝑨 ] using ( refl )
≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ}) (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
 where
  f : hom 𝑨 𝑪                ;  g : hom 𝑪 𝑨
  f = ∘-hom (to ab) (to bc)  ;  g = ∘-hom (from bc) (from ab)

  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans )
  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )

  τ : ∀ b → ∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b) ≈ᶜ b
  τ b = transᶜ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)

  ν : ∀ a → ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a) ≈ a
  ν a = trans (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)
\end{code}
\fi
\paragraph*{Lift-Alg is an algebraic invariant}
The \af{Lift-Alg} operation neatly resolves the technical problem of
universe non-cumulativity because isomorphism classes of algebras are closed under \af{Lift-Alg}; that is,
\ifshort\else

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})
 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})
\end{code}
\fi
\begin{code}

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
\end{code}
\ifshort\else
\begin{code}
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ
\end{code}
\fi

\paragraph*{Homomorphic images}
We have found that the most useful way to encode the concept of \emph{homomorphic image}
is to produce a witness, that is, a surjective hom.  Thus we define the type of surjective homs
and also record the fact that an algebra is its own homomorphic image via the identity
hom.\footnote{Here and elsewhere we use the shorthand \af{ov}~\ab{α} := \ab{𝒪}
\ap{⊔} \ab{𝒱} \ap{⊔} \ab{α}, for any level \ab{α}.}

\ifshort\else
\begin{code}

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α
\end{code}
\fi
\begin{code}

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )
\end{code}
\ifshort\else    %%% BEGIN LONG VERSION ONLY

\medskip

\noindent These types should be self-explanatory, but just to be sure, we pause
to describe the semantics of the Sigma type appearing in the definition of \af{HomImages}.
If \ab{𝑨} : \af{Algebra} \ab{α} \ab{ρᵃ} is an \ab{𝑆}-algebra, then \af{HomImages} \ab{𝑨}
denotes the type of pairs (\ab{𝑩} \aic{,} \ab p) such that \ab{𝑩} : \ar{Algebra} \ab{β} \ab{ρᵇ}
and \ab p is a proof that there exists a hom from \ab{𝑨} onto \ab{𝑩}.
\fi      %%% END LONG VERSION ONLY SECTION

%% -------------------------------------------------------------------------------------
\subsection{Subalgebras}
\label{subalgebras}
Given \ab{𝑆}-algebras \ab{𝑨} and \ab{𝑩}, we say that \ab{𝑨} is a \defn{subalgebra} of
\ab{𝑨}, and we write \ab{𝑨}~\aof{≤}~\ab{𝑩}, just in case \ab{𝑨} can be \emph{homomorphically
embedded} in \ab{𝑩}; in other terms, \ab{𝑨}~\aof{≤}~\ab{𝑩} if and only if there exists an injective
hom from \ab{𝑨} to \ab{𝑩}.

\begin{code}

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

\end{code}
The subalgebra relation is a \defn{preorder}, that is, a reflexive (by the identity monomorphism), and
transitive (by composition of monomorphisms) relation.
\begin{code}

≤-reflexive   :  {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id

≤-transitive  :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ}
 →               𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
≤-transitive ( f , finj ) ( g , ginj ) = (∘-hom f g ) , ∘-IsInjective ∣ f ∣ ∣ g ∣ finj ginj

\end{code}
\noindent If
\ab{𝒜} : \ab I → \af{Algebra} \ab{α} \ab{ρᵃ},
\ab{ℬ} : \ab I → \af{Algebra} \ab{β} \ab{ρᵇ} (families of \ab{𝑆}-algebras) and
\ab{ℬ} \ab i \af{≤} \ab{𝒜} \ab i for all \ab i~:~\ab I, then \af{⨅} \ab{ℬ} is a subalgebra
of \af{⨅} \ab{𝒜}.
\ifshort
Below we use \af{⨅-≤} to denote this fact.
\else

\begin{code}
module _ {ι : Level} {I : Type ι}{𝒜 : I → Algebra α ρᵃ}{ℬ : I → Algebra β ρᵇ} where

 ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
 ⨅-≤ B≤A = (hfunc , hhom) , hM
  where
  hi : ∀ i → hom (ℬ i) (𝒜 i)
  hi = fst ∘ B≤A
  hfunc : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
  (hfunc ⟨$⟩ x) i = ∣ hi i ∣ ⟨$⟩ x i
  cong hfunc = λ xy i → cong ∣ hi i ∣ (xy i)
  hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
  compatible hhom = λ i → compatible ∥ hi i ∥
  hM : IsInjective hfunc
  hM = λ xy i → ∥ B≤A i ∥ (xy i)

\end{code}

We conclude this section with two easy facts that will be useful later. The first converts a monomorphism
to a subalgebra witness while the second is an algebraic invariance property of \aof{≤}.

\begin{code}

mon→≤      :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

≅-trans-≤  :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ}
 →            𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-IsInjective ∣ to A≅B ∣ ∣ h ∣ (toIsInjective A≅B) hinj)
\end{code}
\fi

%% -------------------------------------------------------------------------------------

\subsection{Terms}
\label{terms}
Fix a signature \ab{𝑆} and let \ab X denote an arbitrary nonempty collection of variable
symbols. Such a collection is called a \defn{context}.
Assume the symbols in \ab X are distinct from the operation symbols of
\ab{𝑆}, that is \ab X \aof{∩} \aof{∣} \ab{𝑆} \aof{∣} = ∅.
A \defn{word} in the language of \ab{𝑆} is a finite sequence of members of \ab X \aof{∪}
\aof{∣~\ab{𝑆}~∣}. We denote the concatenation of such sequences by simple juxtaposition.
Let \ab{S₀} denote the set of nullary operation symbols of \ab{𝑆}. We define by induction
on \textit{n} the sets \ab{𝑇ₙ} of \emph{words} over \ab X \aof{∪} \aof{∣~\ab{𝑆}~∣} as
follows (cf.~\cite[Def. 4.19]{Bergman:2012}): \ab{𝑇₀} := \ab X \aof{∪} \ab{S₀} and
\ab{𝑇ₙ₊₁} := \ab{𝑇ₙ} \aof{∪} \ab{𝒯ₙ}, where \ab{𝒯ₙ} is the collection of all \ab f \ab t
such that \ab f : \aof{∣~\ab{𝑆}~∣} and \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→}
\ab{𝑇ₙ}.
\ifshort\else
(Recall, \aof{∥~\ab{𝑆}~∥} \ab f is the arity of the operation symbol \ab f.)
\fi
An \ab{𝑆}-\defn{term} is a term in the language of \ab{𝑆} and the collection of all
\ab{𝑆}-\defn{terms} in the context \ab X is given by \Term{X} := \aof{⋃ₙ} \ab{𝑇ₙ}.

In type theory, this translates to two cases: variable injection and applying an
operation symbol to a tuple of terms. This represents each term as a tree
with an operation symbol at each \aic{node} and a variable symbol at each leaf \aic{ℊ};
hence the constructor names (\aic{ℊ} for ``generator'' and \aic{node} for ``node'') in the
following inductively defined type.

\begin{code}

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X
\end{code}

\paragraph*{The term algebra}
We enrich the \ad{Term} type to a setoid of  \ab{𝑆}-terms, which will ultimately
be used as the domain of an algebra, called the \emph{term algebra in the signature} \ab{𝑆}.
For this we need an equivalence relation on terms.

\ifshort\else
\begin{code}

module _ {X : Type χ } where
\end{code}
\fi
\begin{code}

 data _≃_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)

\end{code}
It is straightforward to show that \ad{\au{}≃\au{}} is an equivalence relation,
\ifshort
and we refer to this fact as \af{≃-isEquiv} below.
\else
as follows.

\begin{code}

 ≃-isRefl   : Reflexive      _≃_
 ≃-isRefl {ℊ _} = rfl ≡.refl
 ≃-isRefl {node _ _} = gnl (λ _ → ≃-isRefl)

 ≃-isSym    : Symmetric      _≃_
 ≃-isSym (rfl x) = rfl (≡.sym x)
 ≃-isSym (gnl x) = gnl (λ i → ≃-isSym (x i))

 ≃-isTrans  : Transitive     _≃_
 ≃-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≃-isTrans (gnl x) (gnl y) = gnl (λ i → ≃-isTrans (x i) (y i))

 ≃-isEquiv  : IsEquivalence  _≃_
 ≃-isEquiv = record { refl = ≃-isRefl ; sym = ≃-isSym ; trans = ≃-isTrans }
\end{code}
\fi

We now define, for a given signature \ab{𝑆} and context \ab X,
%if the type \Term{X} is nonempty (equivalently, if \ab X or
%\aof{∣~\ab{𝑆}~∣} is nonempty), then
the algebraic structure \T{X}, known as the \defn{term algebra in} \ab{𝑆} \defn{over} \ab
X.  Terms are viewed as acting on other terms, so both the elements of the domain of \T{X}
and its basic operations are terms themselves. That is, for each operation symbol \ab
f : \aof{∣~\ab{𝑆}~∣}, we denote by \ab f~\aof{̂}~\T{X} the operation on \Term{X} that maps
each tuple of terms, say, \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→} \Term{X}, to the formal
term \ab f \ab t.
%We let \T{X} denote the term algebra in \ab{𝑆} over \ab X; it has universe \Term{X} and
%operations \ab f \aof{̂} (\T{X}), one for each symbol \ab f in \aof{∣~\ab{𝑆}~∣}.

\begin{code}

TermSetoid : (X : Type χ) → Setoid _ _
TermSetoid X = record { Carrier = Term X ; _≈_ = _≃_ ; isEquivalence = ≃-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≃ts) = gnl ss≃ts
\end{code}

\paragraph*{Substitution, environments and interpretation of terms}
The approach to formalizing these three concepts is based on similar code developed by
Andreas Abel to formalize Birkhoff's completeness theorem~\cite{Abel:2021}.
\ifshort\else

Recall that the domain of an algebra \ab{𝑨} is a setoid, which we denote by
\af{𝔻[~\ab{𝑨}~]}, whose \afld{Carrier} is the carrier of the algebra, \af{𝕌[~\ab{𝑨}~]},
and whose equivalence relation represents equality of elements in \af{𝕌[~\ab{𝑨}~]}.
\fi
\af{Sub} performs substitution from one context to
another.  Specifically, if \ab X and \ab Y are contexts, then \af{Sub} \ab X \ab Y
assigns a term in \ab X to each symbol in \ab Y.
A substitution \ab{σ} applied to a term \ab t is denoted by \af{[~\ab{σ}~]} \ab t.

\begin{code}

Sub : Type χ → Type χ → Type _
Sub X Y = (y : Y) → Term X

[_]_ : {X Y : Type χ} → Sub X Y → Term Y → Term X
[ σ ] (ℊ x) = σ x
[ σ ] (node f ts) = node f (λ i → [ σ ] (ts i))

\end{code}

Fix a signature \ab{𝑆}, a context \ab X, and an \ab{𝑆}-algebra \ab{𝑨}.
An \defn{environment} \ab{𝑨} for \ab X is an \ab X indexed family of setoids,
where the equivalence is taken pointwise.

\begin{code}

module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )

 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ τ → (x : X) → ρ x ≈ τ x
                 ; isEquivalence = record  { refl   = λ _      → refl
                                           ; sym    = λ h x    → sym (h x)
                                           ; trans  = λ g h x  → trans (g x)(h x) }}

\end{code}
As the above definition, as well as the next, are relative to a fixed algebra, we use
a submodule to succinctly capture this commonality in the definitions.
The function \af{⟦\au{}⟧} then denotes the \defn{interpretation} of
a term in a given algebra, \emph{evaluated} in a given environment.

\begin{code}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v          = u≈v x
 cong ⟦ node f args ⟧ x≈y  = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}

Two terms are proclaimed \defn{equal} if they are equal for all
environments.  We represent this equivalence of terms
\ifshort\else
and proof that it is an equivalence relation,
\fi
as follows.

\begin{code}

 Equal : {X : Type χ}(s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

\end{code}
\ifshort
Proof that \af{Equal} is an equivalence relation, and that the implication \ab
s~\af{≃}~\ab t \as{→} \af{Equal} \ab s \ab t holds for all terms \ab s and \ab t, is
straightforward (\seemedium).
(We denote these by \af{EqualIsEquiv} and \af{≃→Equal} in the sequel.)
\else
\begin{code}
 ≃→Equal : {X : Type χ}(s t : Term X) → s ≃ t → Equal s t
 ≃→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≃→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≃→Equal(s i)(t i)(x i)ρ )

 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 reflᵉ   EqualIsEquiv = λ _        → refl
 symᵉ    EqualIsEquiv = λ x=y ρ    → sym (x=y ρ)
 transᵉ  EqualIsEquiv = λ ij jk ρ  → trans (ij ρ) (jk ρ)

\end{code}
\fi

We can then prove that substitution and evaluation commute.  More precisely,
applying substitution \ab{σ} to a term \ab{t}
and evaluating the result in environment \ab{ρ} has the same effect as evaluating
\ab{t} in the environment \as{λ} \ab x \as{→} \aof{⟦~\ab{σ}~\ab{x}~⟧}~\aofld{⟨\$⟩}
\ab{ρ} (see~\cite{Abel:2021} or~\cite[Lem.~3.3.11]{Mitchell:1996}).

\begin{code}

 substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
  →              ⟦ [ σ ] t ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ (λ x → ⟦ σ x ⟧ ⟨$⟩ ρ)
 substitution (ℊ x)        σ ρ = refl
 substitution (node f ts)  σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)

\end{code}

\ifshort\else
\paragraph*{Compatibility of terms}
\fi
We need to formalize two more concepts involving terms.
The first is the assertion that every term commutes with every homomorphism (\af{comm-hom-term}), and
the second is the interpretation of a term in a product algebra (\af{interp-prod}).
\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Environment 𝑨                           using ( ⟦_⟧         )
 open Environment 𝑩 renaming ( ⟦_⟧ to ⟦_⟧ᴮ )  using (             )
 open Setoid 𝔻[ 𝑩 ]                           using ( _≈_ ; refl  )
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a       =     refl
 comm-hom-term (node f t) a  =     begin
  h(⟦ node f t ⟧ ⟨$⟩ a)            ≈⟨ compatible ∥ hh ∥ ⟩
  (f ̂ 𝑩)(λ i → h(⟦ t i ⟧ ⟨$⟩ a))  ≈⟨ cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term (t i) a)⟩
  ⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a)        ∎ where  open SetoidReasoning 𝔻[ 𝑩 ]

module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]  using ( _≈_ )
 open Environment      using ( ⟦_⟧ ; ≃→Equal )

 interp-prod : (p : Term X) → ∀ ρ →  (⟦ ⨅ 𝒜 ⟧ p) ⟨$⟩ ρ   ≈   λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x)       = λ ρ i  → ≃→Equal (𝒜 i) (ℊ x) (ℊ x) ≃-isRefl λ _ → (ρ x) i
 interp-prod (node f t)  = λ ρ    → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )
\end{code}

\section{Equational Logic}
\label{equational-logic}

\paragraph*{Term identities, equational theories, and the ⊧ relation}
Given a signature \ab{𝑆} and a context \ab X, an \ab{𝑆}-\defn{term equation} or \ab{𝑆}-\defn{term identity}
is an ordered pair (\ab p , \ab q) of 𝑆-terms, also denoted by \ab p \af{≈} \ab q.
They are often simply called equations or identities, especially when the signature \ab{𝑆} is clear.

We define an \defn{equational theory} (or \defn{algebraic theory}) to be a pair \ab{T} =
(\ab{𝑆} , \ab{ℰᵀ}) consisting of a signature \ab{𝑆} and a collection \ab{ℰᵀ} of
\ab{𝑆}-term equations. Some authors reserve the term \defn{theory} for
a \emph{deductively closed} set of equations, that is, a set of equations that is closed
under \emph{entailment} (defined below).

We say that the algebra \ab{𝑨} \emph{satisfies} the equation \ab p \af{≈} \ab q if,
for all \ab{ρ} : \ab X \as{→} \aof{𝔻[~\ab{𝑨}~]},
%(assigning values in the domain of \ab{𝑨} to variable symbols in \ab X)
we have \aof{⟦~\ab{p}~⟧} \aofld{⟨\$⟩} \ab{ρ} \af{≈} \aof{⟦~\ab{q}~⟧} \aofld{⟨\$⟩} \ab{ρ}.
In other words, when they are interpreted in the algebra \ab{𝑨},
the terms \ab{p} and \ab{q} are equal no matter what values in \ab{𝑨} are assigned to variable symbols in \ab{X}.
In this situation, we write
\ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q} and say that \ab{𝑨} \defn{models} \ab{p}~\af{≈}~\ab{q},
or that \ab{𝑨} is a \defn{model} of \ab{p}~\af{≈}~\ab{q}.
If \ab{𝒦} is a class of algebras, all of the same signature, we write \ab{𝒦}~\aof{⊫}~\ab{p}~\aof{≈}~\ab{q}
and say that \ab{𝒦} \defn{models} the identity \ab{p}~\af{≈}~\ab{q} provided for every \ab{𝑨} \aof{∈} \ab{𝒦}
we have \ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q}.

\ifshort\else
\begin{code}
module _ {X : Type χ} where
\end{code}
\fi
\begin{code}

 _⊧_≈_ : Algebra α ρᵃ → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = Equal p q where open Environment 𝑨

 _⊫_≈_ : Pred (Algebra α ρᵃ) ℓ → Term X → Term X → Type _
 𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}
We represent a set of identities as a predicate over pairs of
terms, say, \ab{ℰ} : \af{Pred}(\ad{Term} \ab{X} \af{×} \ad{Term} \ab{X})~\au{}  and we denote by
\ab{𝑨}~\aof{⊨}~\ab{ℰ} the assertion that the algebra \ab{𝑨} models \ab{p}~\af{≈}~\ab{q}
for all (\ab{p} , \ab{q}) \af{∈} \ab{ℰ}.\footnote{Notice that \af{⊨} is
a stretched version of the models symbol, \af{⊧}%
\ifshort
.
\else
; this makes it possible for \agda to distinguish and parse expressions involving the types
\af{\au{}⊨\au{}} and \af{\au{}⊧\au{}≈\au{}}.
In Emacs \texttt{agda2-mode}, the symbol \af{⊨} is produced by typing
\textbackslash\textbar{}=, while \af{⊧} is
produced with \textbackslash{}models.
\fi
}

\begin{code}

 _⊨_ : (𝑨 : Algebra α ρᵃ) → Pred(Term X × Term X)(ov χ) → Type _
 𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

\end{code}

If \ab{𝒦} is a class of structures and \ab{ℰ} a set of term identities, then the set of
term equations modeled by \ab{𝒦} is denoted by \af{Th}~\ab{𝒦} and is called the
\defn{equational theory} of \ab{𝒦}, while the class of structures modeling \ab{ℰ} is
denoted by \af{Mod}~\ab{ℰ} and is called the \defn{equational class axiomatized} by
\ab{ℰ}.

\begin{code}

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
\end{code}

\paragraph*{Entailment}

If \ab{ℰ} is a set of \ab{𝑆}-term equations and \ab{p} and \ab{q} are \ab{𝑆}-terms,
we say that \ab{ℰ} \defn{entails} the equation \ab{p}~\aof{≈}~\ab{q}, and we write
\ab{ℰ}~\ad{⊢}~\ab{p}~\ad{≈}~\ab{q}, just in case every model of \ab{ℰ} also models
\ab{p}~\aof{≈}~\ab{q}.
We model our definition of \defn{entailment type} on the one defined by Abel
in~\cite{Abel:2021}.  It contains cases for representing hypotheses, congruence of term
application, that substitution respects entailment, and that entailment is
an equivalence.

\begin{code}

data _⊢_▹_≈_  (ℰ : {Y : Type χ} → Pred(Term Y × Term Y) (ov χ)) :
              (X : Type χ)(p q : Term X) → Type (ov χ) where

 hyp         :  ∀{Y}{p q : Term Y} → (p , q) ∈ ℰ → ℰ ⊢ _ ▹ p ≈ q
 app         :  ∀{Y}{ps qs : ∥ 𝑆 ∥ 𝑓 → Term Y}
                          → (∀ i → ℰ ⊢ Y ▹ ps i ≈ qs i) → ℰ ⊢ Y ▹ (node 𝑓 ps) ≈ (node 𝑓 qs)
 sub         :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → (σ : Sub Δ Γ) → ℰ ⊢ Δ ▹ ([ σ ] p) ≈ ([ σ ] q)
 reflexive   :  ∀{p}      → ℰ ⊢ Γ ▹ p ≈ p
 symmetric   :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ p
 transitive  :  ∀{p q r}  → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r → ℰ ⊢ Γ ▹ p ≈ r

\end{code}

The fact that this exactly represents the informal semantic notion of entailment
given earlier is called \defn{soundness} and
\defn{completeness}.
More precisely, \defn{the entailment type is sound} means that
if \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\ad{≈}~\ab q, then \ab p \aof{≈} \ab q holds in
every model of \ab{ℰ}.
\defn{The entailment type is complete} means that
if \ab p \aof{≈} \ab q holds in every model of \ab{ℰ},
then \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\aof{≈}~\ab q.
We will use soundness of entailment only once below%
\ifshort
~(by the name \af{sound}), so we omit its proof, but see~\cite{Abel:2021}
or~\cite{DeMeo:2021}.
\else
; nonetheless, here is its formalization (essentially due to Abel, \textit{op. cit.}):

\begin{code}

module Soundness  (ℰ : {Y : Type χ} → Pred(Term Y × Term Y) (ov χ))
                  (𝑨 : Algebra α ρᵃ)                -- We assume an algebra 𝑨
                  (V : ∀{Y} → _⊨_{χ = χ} 𝑨 (ℰ{Y}))  -- that models all equations in ℰ.
                  where
 open SetoidReasoning 𝔻[ 𝑨 ]
 open Environment 𝑨
 sound : ∀ {p q} → ℰ ⊢ Γ ▹ p ≈ q → 𝑨 ⊧ p ≈ q
 sound (hyp i) = V i
 sound (app es) ρ = cong (Interp 𝑨) (≡.refl , λ i → sound (es i) ρ)
 sound (sub {p = p}{q} Epq σ) ρ =
  begin
   ⟦ [ σ ] p  ⟧ ⟨$⟩                     ρ   ≈⟨   substitution p σ ρ               ⟩
   ⟦ p        ⟧ ⟨$⟩ (λ x → ⟦ σ x ⟧ ⟨$⟩  ρ)  ≈⟨   sound Epq (λ x → ⟦ σ x ⟧ ⟨$⟩ ρ)  ⟩
   ⟦ q        ⟧ ⟨$⟩ (λ x → ⟦ σ x ⟧ ⟨$⟩  ρ)  ≈˘⟨  substitution q σ ρ               ⟩
   ⟦ [ σ ] q  ⟧ ⟨$⟩                     ρ   ∎
 sound (reflexive   {p = p}                 ) = reflᵉ   EqualIsEquiv {x = p}
 sound (symmetric   {p = p}{q}     Epq      ) = symᵉ    EqualIsEquiv {x = p}{q}     (sound Epq)
 sound (transitive  {p = p}{q}{r}  Epq Eqr  ) = transᵉ  EqualIsEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
\end{code}
\fi

\paragraph*{The Closure Operators H, S, P and V}
Fix a signature \ab{𝑆}, let \ab{𝒦} be a class of \ab{𝑆}-algebras, and define
\begin{itemize}
\item \af H \ab{𝒦} = algebras isomorphic to homomorphic images of members of \ab{𝒦};
\item \af S \ab{𝒦} = algebras isomorphic to subalgebras of members of \ab{𝒦};
\item \af P \ab{𝒦} = algebras isomorphic to products of members of \ab{𝒦}.
\end{itemize}
\ifshort\else
A straight-forward verification confirms that
\fi
\af H, \af S, and \af P are \emph{closure operators} (expansive, monotone, and
idempotent).  A class \ab{𝒦} of \ab{𝑆}-algebras is said to be \emph{closed under
the taking of homomorphic images} provided \af H \ab{𝒦} \aof{⊆} \ab{𝒦}. Similarly, \ab{𝒦} is
\emph{closed under the taking of subalgebras} (resp., \emph{arbitrary products}) provided
\af S~\ab{𝒦}~\aof{⊆}~\ab{𝒦} (resp., \af P \ab{𝒦} \aof{⊆} \ab{𝒦}). The operators \af H, \af
S, and \af P can be composed with one another repeatedly, forming yet more closure
operators.

% An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic.
% Thus, the class \af H \ab{𝒦} (resp., \af S \ab{𝒦}; resp., \af P \ab{𝒦}) is closed under isomorphism.

A \emph{variety} is a class of \ab{𝑆}-algebras that is closed under the taking of
homomorphic images, subalgebras, and arbitrary products.  To represent varieties
we define closure operators \af H, \af S, and \af P that are composable; we
then define a type \af V which represents closure under all three.
Thus, if \ab{𝒦} is a class of \ab{𝑆}-algebras, then
\af V \ab{𝒦} := \af H (\af S (\af P \ab{𝒦})), and \ab{𝒦} is a variety if and only if \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.
\ifshort\else

We now define the type \af H to represent classes of algebras that include all homomorphic images
of algebras in the class---i.e., classes that are closed under the taking of homomorphic
images---the type \af S to represent classes of algebras that closed under the taking of subalgebras,
and the type \af P to represent classes of algebras closed under the taking of arbitrary products.

\begin{code}

module _ {α ρᵃ β ρᵇ : Level} where
\end{code}
\fi
\begin{code}

 private a = α ⊔ ρᵃ
 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

\end{code}
Finally, we define the \defn{varietal closure} of a class \ab{𝒦} to be the class \af{V}
\ab{𝒦} := \af{H} (\af{S} (\af{P} \ab{𝒦})).  The explicit universe level declarations
are needed for disambiguation.
\begin{code}

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ
 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

\end{code}

An important property of the binary relation \aof{⊧} is \emph{algebraic invariance} (i.e.,
invariance under isomorphism).  We formalize this result as follows.

\ifshort\else
\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where
\end{code}
\fi
\begin{code}

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ = begin
      ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
      ⟦ p ⟧   ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
    f(⟦ p ⟧ᴬ  ⟨$⟩        (g  ∘  ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
    f(⟦ q ⟧ᴬ  ⟨$⟩        (g  ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
      ⟦ q ⟧   ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
      ⟦ q ⟧   ⟨$⟩               ρ    ∎
  where
  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
  open Environment 𝑨     using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩     using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]

\end{code}
Identities modeled by an algebra \ab{𝑨} are also modeled by every homomorphic image of
\ab{𝑨} and by every subalgebra of \ab{𝑨}.
\ifshort
We refer to these facts as \af{⊧-H-invar} and \af{⊧-S-invar}, but omit their formal
statements and proofs, which are analogous to those of \af{⊧-I-invar}.
\else
These facts are formalized in \agda as follows.

\ifshort\else
\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where
\end{code}
\fi
\begin{code}

 ⊧-H-invar : 𝑨 ⊧ p ≈ q → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-H-invar Apq (φh , φE) ρ =
  begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong ∣ φh ∣ (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎
  where
  φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
  φ⁻¹ = SurjInv ∣ φh ∣ φE
  private φ = (_⟨$⟩_ ∣ φh ∣)
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
  open Environment 𝑩  using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]

 ⊧-S-invar : 𝑨 ⊧ p ≈ q → 𝑩 ≤ 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = ∥ B≤A ∥
  ( begin
    h (  ⟦ p ⟧   ⟨$⟩       b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ  ⟨$⟩ (h ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
    h (  ⟦ q ⟧   ⟨$⟩       b)  ∎ )
  where
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  private hh = ∣ B≤A ∣ ; h = _⟨$⟩_ ∣ hh ∣

\end{code}
\fi
An identity satisfied by all algebras in an indexed collection is
also satisfied by the product of algebras in the collection.
\ifshort
We refer to this fact as \af{⊧-P-invar}.
\else

\begin{code}

module _ {X : Type χ}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ){p q : Term X} where
 ⊧-P-invar : (∀ i → 𝒜 i ⊧ p ≈ q) → ⨅ 𝒜 ⊧ p ≈ q
 ⊧-P-invar 𝒜pq a =
  begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨ (λ i → 𝒜pq i (λ x → (a x) i)) ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a  ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎
  where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]

\end{code}
\fi

The classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦}, and \af V \ab{𝒦} all satisfy the
same term identities.  We will only use a subset of the inclusions needed to prove this
assertion, and we present here just the facts we need.\footnote{For more details, see
\ualmodule{Setoid.Varieties.Preservation}.}
First, the closure operator \af H preserves the identities modeled by the
given class; this follows almost immediately from the invariance lemma
\af{⊧-H-invar}.

\ifshort\else
\begin{code}

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
\end{code}
\fi
\begin{code}

 H-id1 : 𝒦 ⊫ p ≈ q → H{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA

\end{code}
The analogous preservation result for \af S is a consequence of
the invariance lemma \af{⊧-S-invar}; the converse, which we call
\af{S-id2}, has an equally straightforward proof.

\begin{code}

 S-id1 : 𝒦 ⊫ p ≈ q → S{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

\end{code}
Finally, we have analogous pairs of implications for \af P, \af H, and \af V,
  called \af{P-id1}, \af{P-id2}, \af{H-id1}, etc.
\ifshort
We omit the formalizations (\seeshort).
\else
In each case, we will only need the first implication, so we omit the others from this presentation.

\begin{code}

 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P{β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} (λ i → σ (𝒜 i) (kA i))

module _ {X : Type χ}{ι : Level}(ℓ : Level){𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA))
   where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ p ≈ q
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
\end{code}
\fi

%% -------------------------------------------------------------------------------------

\section{Free Algebras}
\label{free-algebras}
\paragraph*{The absolutely free algebra}
The term algebra \af{𝑻} \ab X is the \emph{absolutely free} (or \emph{initial})
\ab{S}-algebra. That is, for every \ab{𝑆}-algebra \ab{𝑨}, the following hold.
\begin{itemize}
\item Every function from \ab{X} to \af{𝕌[ \ab{𝑨} ]} lifts to a homomorphism from \af{𝑻} \ab{X} to \ab{𝑨}.
\item That homomorphism is unique.
\end{itemize}
We formalize the first of these in two steps.\footnote{\agdaalgebras also defines
 \af{free-lift-func} \as{:} \aof{𝔻[~\af{𝑻}~\ab X~]}~\aor{⟶}~\aof{𝔻[~\ab{𝑨}~]}
 for the analogous setoid function.}$^,$\footnote{For the proof of uniqueness,
see \ualmodule{Setoid.Terms.Properties}.}  First is the lifting (\af{free-lift}).
\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

\end{code}
\ifshort\else
\begin{code}
 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , (λ i → flcong (x i)))

\end{code}
\fi
\ifshort\else
At the base step, when the term has the form \aic{ℊ}
\ab x, the free lift of \ab h agrees with \ab h; at the inductive step, when the
term has the form \aic{node} \ab f \ab t, we assume (the induction hypothesis)
that the image of each subterm \ab t \ab i under the free lift of \ab h is known
and the free lift is defined by applying \ab f \aof{̂} \ab{𝑨} to these images.
\fi
Then the lift so defined is shown to be a homomorphism.

\begin{code}

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func ,
   mkhom (λ{_}{a} → cong (Interp 𝑨) (≡.refl , (λ i → (cong free-lift-func){a i} ≃-isRefl)))

\end{code}

It turns out that the interpretation of a term \ab p in an environment \ab{η} is the same
as the free lift of \ab{η} evaluated at \ab p. We apply this fact a number of times in the sequel.

\ifshort\else
\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ} where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )
\end{code}
\fi
\begin{code}

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}

\paragraph*{The relatively free algebra in theory}
Here we mathematically describe, for a given class \ab{𝒦} of \ab{𝑆}-algebras, the
\emph{relatively free algebra} in \af{S} (\af{P} \ab{𝒦}) over \ab X, with the
type theoretic version to follow in the next section.

Recall that the term algebra \T{X} is the \emph{free} class of all
\ab{𝑆}-algebras. Given an arbitrary class \ab{𝒦} of \ab{𝑆}-algebras, we can't expect that
\T{X} belongs to \ab{𝒦}, so, in general, we say that \T{X} is free \emph{for} \ab{𝒦}.
\ifshort\else
Indeed, it might not be possible to find a free algebra that belongs to \ab{𝒦}.
\fi
However, for any class \ab{𝒦} we can construct an algebra that is free for \ab{𝒦}
and belongs to the class \af{S} (\af{P} \ab{𝒦}), and for most applications this suffices.

The construction of the free algebra in \af{S} (\af{P} \ab{𝒦})
proceeds by taking the quotient of \T{X} modulo a congruence relation \afld{≈}.  One approach is to let
\afld{≈} be \af{⋂}\{\ab{θ} \af{∈} \af{Con} (\T{X}) : \T{X} \af{/} \ab{θ} \af{∈} \af{S}
\ab{𝒦}\}.\footnote{\af{Con} (\T{X}) denotes the congruences of \T{X}.}

\ifshort\else
Equivalently, we could let \ab{ℰ} = \af{Th} \ab{𝒦} and take \afld{≈} to be the least equivalence relation
on the domain of \T{X} such that
\begin{enumerate}
\item for every equation (\ab p , \ab q) \af{∈} \af{Th} \ab{𝒦} and every
environment \ab{ρ} : \ab X \as{→} \Term{X}, we have\\
\af{⟦~\ab p~⟧} \afld{⟨\$⟩} \ab{ρ} \afld{≈} \af{⟦~\ab q~⟧} \afld{⟨\$⟩} \ab{ρ}, and
\item \afld{≈} is a congruence of \T{X}; that is, for every operation symbol \ab
f : \af{∣~\ab{𝑆}~∣}, and for all tuples \ab{s} \ab{t} : \af{∥~\ab{𝑆}~∥} \ab f
→ \Term{X}, the following implication holds:\footnote{Here all
interpretations, denoted by \af{⟦\au{}⟧}, are with respect to \T{X}.}\\[-8pt]

(∀ i → \af{⟦~\ab{s}~\ab i~⟧}~\afld{⟨\$⟩}~\ab{ρ}~\afld{≈}~\af{⟦~\ab{t}~\ab
i~⟧}~\afld{⟨\$⟩}~\ab{ρ})
\as{→} \af{⟦~\ab f~\ab s~⟧}~\afld{⟨\$⟩}~\ab{ρ}~\afld{≈}~\af{⟦~\ab f~\ab
t~⟧}~\afld{⟨\$⟩}~\ab{ρ}\\[-8pt]
\end{enumerate}
\fi

The \defn{relatively free algebra over} \ab{X} (relative to
\ab{𝒦}) is defined to be the quotient \Free{X} := \T{X}~\af{/}~\afld{≈}.
Evidently, \Free{X} is a subdirect product of the algebras in \{\T{X}~\af{/}~\ab{θ}\!\},
where \ab{θ} ranges over congruences modulo which \T{X} belongs to \af{S}~\ab{𝒦}.
In particular, \Free{X} embeds in a product of members of \af{S}~\ab{𝒦}, so
\Free{X} \af{∈} \af{S}(\af{P}(\af{S}~\ab{𝒦})) ⊆ \af{S}(\af{P}~\ab{𝒦}). It follows
that \Free{X} satisfies the identities in \af{Th} \ab{𝒦} (those modeled by all members of
\ab{𝒦}).  Indeed, for each pair \ab p \ab q : \Term{X}, if \ab{𝒦} \af{⊫} \ab p \af{≈} \ab
q, then \ab p and \ab q belong to the same \afld{≈}-class, so \ab p and \ab q are
identified in \Free{X}. \ifshort\else (Notice that \afld{≈} may be empty, in which case
\T{X}~\af{/}~\afld{≈} is trivial.) \fi

\paragraph*{The relatively free algebra in \agda}
%Our approach looks a bit different from the informal one described above, because we
%represent quotients as setoids, but the end result is the same.
We start with a type \ab{ℰ} representing a collection of identities and, instead of
forming a quotient, we take the domain of the free algebra to be a setoid whose
\afld{Carrier} is the type \Term{X} of {𝑆}-terms in \ab X and whose equivalence relation
includes all pairs (\ab p , \ab q) \af{∈} \Term{X} \af{×} \Term{X} such that \ab p \aod{≈}
\ab q is derivable from \ab{ℰ}; that is, \ab{ℰ} \aod{⊢} \ab X \aod{▹} \ab p \aod{≈} \ab q.
Observe that elements of this setoid are equal iff they belong to the same equivalence
class of the congruence \afld{≈} defined above.  Therefore, the setoid so defined, which
we denote by \Free{X}, represents the quotient \T{X}~\af{/}~\afld{≈}.
Finally, the interpretation of an operation in the free algebra is simply the operation
itself, which works since \ab{ℰ} \aod{⊢} \ab X \aod{▹\au{}≈\au{}} is a congruence
relation (see also~\cite{Abel:2021}).

\begin{code}

module FreeAlgebra {χ : Level}(ℰ : {Y : Type χ} → Pred (Term Y × Term Y) (ov χ)) where

 FreeDomain : Type χ → Setoid _ _
 FreeDomain X =
  record  { Carrier        = Term X
          ; _≈_            = ℰ ⊢ X ▹_≈_
          ; isEquivalence  = record { refl = reflexive ; sym = symmetric ; trans = transitive } }

 𝔽[_] : Type χ → Algebra (ov χ) _
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp where
  FreeInterp : ∀ {X} → ⟨ 𝑆 ⟩ (FreeDomain X) ⟶ FreeDomain X
  FreeInterp ⟨$⟩ (f , ts)       = node f ts
  cong FreeInterp (≡.refl , h)  = app h
\end{code}

\paragraph*{The natural epimorphism} % from 𝑻 X to 𝔽[ X ]}
We now define the natural epimorphism from \T{X} onto \Free{X} %(= \T{X}~\af{/}~\afld{≈})
and prove that its kernel is contained in the collection of identities modeled
by \af{V} \ab{𝒦}.%(which we represent by \af{Th} (\af{V} \ab{𝒦})).
\ifshort%
\footnote{The \AgdaFunction{HomReduct} method of the \ar{IsEpi} record type merely extracts the \af{hom} part of an epimorphism.}
\else

\begin{code}

module FreeHom {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra {χ = c} (Th 𝒦) using ( 𝔽[_] )
\end{code}
\fi
\begin{code}

 epiF[_] : (X : Type c) → epi (𝑻 X) 𝔽[ X ]
 epiF[ X ] = h , hepi
  where
  open Setoid 𝔻[ 𝑻 X ]     using ()        renaming ( _≈_ to _≈₀_  ; refl to reflᵀ )
  open Setoid 𝔻[ 𝔽[ X ] ]  using ( refl )  renaming ( _≈_ to _≈₁_  )

  con : ∀ {x y} → x ≈₀ y → x ≈₁ y
  con (rfl {x}{y} ≡.refl) = refl
  con (gnl {f}{s}{t} x) = cong (Interp 𝔽[ X ]) (≡.refl , con ∘ x)

  h : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝔽[ X ] ]
  h = record { f = id ; cong = con }

  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  compatible (isHom hepi) = cong h reflᵀ
  isSurjective hepi {y} = eq y refl

 homF[_] : (X : Type c) → hom (𝑻 X) 𝔽[ X ]
 homF[ X ] = IsEpi.HomReduct ∥ epiF[ X ] ∥

 kernel-in-theory : {X : Type c} → ker ∣ homF[ X ] ∣ ⊆ Th (V ℓ ι 𝒦)
 kernel-in-theory {X = X} {p , q} pKq 𝑨 vkA = V-id1 ℓ {p = p}{q} (ζ pKq) 𝑨 vkA
  where
  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨

\end{code}
Next we prove an important property of the relatively free algebra
(relative to \ab{𝒦} and satisfying the identities in \af{Th} \ab{𝒦}),
which will be used in the formalization of the HSP theorem. Specifically,
we prove that for every algebra \ab{𝑨}, if \ab{𝑨} \af{⊨} \ab{Th} (\af{V} \ab{𝒦}),
then there exists an epimorphism from \Free{A} onto \ab{𝑨}.

\ifshort\else
\begin{code}

module _  {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeHom {ℓ = ℓ} {𝒦}
 open FreeAlgebra {χ = c}(Th 𝒦)  using ( 𝔽[_] )
 open Setoid 𝔻[ 𝑨 ]              using ( refl ; sym ; trans ) renaming  ( Carrier  to A )
\end{code}
\fi
\begin{code}

 F-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] 𝑨
 F-ModTh-epi A∈ModThK = φ , isEpi
  where
  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  =  trans  ( sym (free-lift-interp{𝑨 = 𝑨} id p) )
                     (  trans  ( A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                               ( free-lift-interp{𝑨 = 𝑨} id q ) )
  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  compatible (isHom isEpi) = cong (Interp 𝑨) (≡.refl , (λ _ → refl))
  isSurjective isEpi {y} = eq (ℊ y) refl
\end{code}
\ifshort\else

\medskip

\noindent Actually, we will need the following lifted version of this result.

\begin{code}

 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
\end{code}
\fi


%% -------------------------------------------------------------------------------------

\section{Birkhoff's Variety Theorem}

Birkhoff's variety theorem, also known as the HSP theorem, asserts that a class of algebras
is a variety if and only if it is an equational class.  In this section, we present the
statement and proof of the HSP theorem---first in a style similar to
what one finds in textbooks (e.g.,~\cite[Theorem 4.41]{Bergman:2012}),
and then formally in the language of \mltt.

\subsection{Informal proof}
Let \ab{𝒦} be a class of algebras and recall that \ab{𝒦} is a \emph{variety} provided
\ifshort\else
it is closed under homomorphisms, subalgebras and products; equivalently,
\fi
\af{V} \ab{𝒦} ⊆ \ab{𝒦}.
(Observe that \ab{𝒦} ⊆ \af{V} \ab{𝒦} holds for all \ab{𝒦} since
\af{V} is a closure operator.)
We call \ab{𝒦} an \emph{equational class} if it is precisely the class of all models of some set of identities.

\emph{Every equational class is a variety}. Indeed, suppose \ab{𝒦} is an equational
class axiomatized by term identities \ab{ℰ}; that is, \ab{𝑨} ∈ \ab{𝒦} iff
\ab{𝑨} \af{⊨} \ab{ℰ}. Since the classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦} and
\ab{𝒦} all satisfy the same set of equations, we have \af{V} \ab{𝒦} \af{⊫} \ab p
\af{≈} \ab q for all (\ab p , \ab q) \af{∈} \ab{ℰ}, so \af{V} \ab{𝒦} ⊆ \ab{𝒦}.

The converse assertion---that \emph{every variety is an equational class}---takes more
work.\footnote{The proof we present here is based on that of~\cite[Theorem 4.41]{Bergman:2012}.}
Let \ab{𝒦} be an arbitrary variety.  We will describe a set of equations that axiomatizes
\ab{𝒦}.  A natural choice is \af{Th} \ab{𝒦}, all equations that hold in \ab{𝒦};
% Let \ab{𝒦⁺} := \af{Mod} (\af{Th} \ab{𝒦}). Clearly, \ab{𝒦} \aof{⊆} \ab{𝒦⁺}.  We prove the
for this choice, we must prove \ab{𝒦} \aof{=} \af{Mod} (\af{Th} \ab{𝒦}).
Clearly, \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} \ab{𝒦}).  We prove the
converse inclusion. Let \ab{𝑨} \af{∈} \af{Mod} (\af{Th} \ab{𝒦});
it suffices to find an algebra \ab{𝑭} \af{∈} \af{S} (\af{P} \ab{𝒦}) such that
\ab{𝑨} is a homomorphic image of \ab{𝑭}, as this will show that \ab{𝑨} \af{∈}
\af{H} (\af{S} (\af{P} \ab{𝒦})) = \ab{𝒦}.

Let \ab{X} be such that there exists a \emph{surjective} environment
\ab{ρ} : \ab{X} \as{→} \af{𝕌[~\ab{𝑨}~]}.
%\footnote{This is usually done by assuming \ab{X} has cardinality at least max(|~\af{𝕌[~\ab{𝑨}~]}~|, ω).}
By the \af{lift-hom} lemma, there is an epimorphism \ab{h} from \T{X} onto \af{𝕌[~\ab{𝑨}~]}
that extends \ab{ρ}.
Now, put \aof{𝔽[~\ab{X}~]}~:=~\T{X}/\afld{≈}, and let \ab{g} : \T{X} \as{→} \aof{𝔽[~\ab{X}~]}
be the natural epimorphism with kernel \afld{≈}. We claim that \af{ker} \ab g \af{⊆}
\af{ker} \ab h. If the claim is true, then there is a map \ab{f} : \aof{𝔽[~\ab{X}~]} \as{→} \ab{𝑨}
such that \ab f \af{∘} \ab g = \ab h. Since \ab h is surjective, so is \ab f. Hence \ab{𝑨}
\af{∈} \af{𝖧} (\af{𝔽} \ab X) \aof{⊆} \af{Mod} (\af{Th} \ab{𝒦}) completing the proof.
To prove the claim, let \ab u , \ab v \af{∈} \T{X} and assume that \ab g \ab u =
\ab g \ab v. Since \T{X} is generated by \ab X, there are terms \ab p, \ab q ∈
\T{X} such that \ab u = \af{⟦~\T{X}~⟧} \ab p and v = \af{⟦~\T{X}~⟧} \ab
q.
%\footnote{Recall, \af{⟦~\ab{𝑨}~⟧} \ab t denotes the interpretation of the term
%\ab t in the algebra \ab{𝑨}.}
Therefore,\\[-4pt]

\af{⟦~\Free{X}~⟧} \ab p = \ab g (\af{⟦~\T{X}~⟧} \ab p) = \ab g \ab u = \ab g \ab v =
\ab g (\af{⟦~\T{X}~⟧} \ab q) = \af{⟦~\Free{X}~⟧} \ab q,\\[8pt]
so \ab{𝒦} \af{⊫} \ab p \af{≈} \ab q, thus (\ab p , \ab q) \af{∈} \af{Th}
\ab{𝒦}. Since \ab{𝑨} \af{∈} \af{Mod} (\af{Th} \ab{𝒦}) =
\af{Mod} (\af{Th} \ab{𝒦}), we obtain \ab{𝑨} \af{⊧} \ab p \af{≈} \ab q, which implies
that \ab h \ab u = (\af{⟦~\ab{𝑨}~⟧} \ab p) \aofld{⟨\$⟩} \ab{ρ} = (\af{⟦~\ab{𝑨}~⟧} \ab q)
\aofld{⟨\$⟩} \ab{ρ} = \ab h \ab v, as desired.

\subsection{Formal proof}
We now show how to express and prove the twin assertions that
(i) every equational class is a variety and (ii) every variety is an equational class.

\paragraph*{Every equational class is a variety}
For (i), we need an arbitrary equational class, which we obtain by starting with an arbitrary
collection \ab{ℰ} of equations and then defining \ab{𝒦} = \af{Mod} \ab{ℰ}, the equational class
determined by \ab{ℰ}. We prove that \ab{𝒦} is a variety by showing that
\ab{𝒦} = \af{V} \ab{𝒦}. The inclusion \ab{𝒦} \aof{⊆} \af V \ab{𝒦}, which holds for all
classes \ab{𝒦}, is called the \defn{expansive} property of \af{V}.
\ifshort\else
\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private ι = ov (α ⊔ ρᵃ ⊔ ℓ)
\end{code}
\fi
\begin{code}

 V-expa : 𝒦 ⊆ V ℓ ι 𝒦
 V-expa {x = 𝑨} kA = 𝑨 , (𝑨 , (⊤ , (λ _ → 𝑨) , (λ _ → kA), Goal), ≤-reflexive), IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ] using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ] using () renaming ( refl to refl⨅ )

  to⨅ : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  to⨅ = record { f = λ x _ → x ; cong = λ xy _ → xy }

  from⨅ : 𝔻[ ⨅ (λ _ → 𝑨) ] ⟶ 𝔻[ 𝑨 ]
  from⨅ = record { f = λ x → x tt ; cong = λ xy → xy tt }

  Goal : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal = mkiso (to⨅ , mkhom refl⨅) (from⨅ , mkhom refl) (λ _ _ → refl) (λ _ → refl)

\end{code}
Observe how \ab{𝑨} is expressed as (isomorphic to) a product with just one factor (\ab{𝑨} itself); that is, the product
\AgdaFunction{⨅}\AgdaSpace{}%
\AgdaSymbol{(λ}\AgdaSpace{}%
\AgdaBound{x}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{𝑨}\AgdaSymbol{)}
indexed over the one-element type \af{⊤}.)

The converse inclusion, \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, requires the assumption
that \ab{𝒦} is an equational class. Recall lemma
\af{V-id1}, which asserts that \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q implies \af{V}
\ab{ℓ} \ab{ι} \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q. Whence, if \ab{𝒦} is an equational
class, then \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, as we now confirm.

\begin{code}

module _ {ℓ : Level}{X : Type ℓ}{ℰ : {Y : Type ℓ} → Pred (Term Y × Term Y) (ov ℓ)} where
 private 𝒦 = Mod{α = ℓ}{ℓ}{X} ℰ     -- an arbitrary equational class
 EqCl⇒Var : V ℓ (ov ℓ) 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨} vA {p} {q} pℰq ρ = V-id1 ℓ {𝒦} {p} {q} (λ _ x τ → x pℰq τ) 𝑨 vA ρ

\end{code}
Together, \af{V-expa} and \af{Eqcl⇒Var} prove that every equational class is a variety.


\paragraph*{Every variety is an equational class}
For (ii), we need an arbitrary variety, which we obtain by starting with an arbitrary class
\ab{𝒦} of \ab{𝑆}-algebras and taking the \emph{varietal closure}, \af{V} \ab{𝒦}.
We prove that \af{V} \ab{𝒦} is an equational class by showing it is precisely the collection of
algebras that model the equations in \af{Th} (\af{V} \ab{𝒦}); that is, we prove
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})).
The inclusion \af{V} \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a
consequence of the fact that \af{Mod} \af{Th} is a closure operator.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p} {q} x ρ = x 𝑨 vA ρ

\end{code}

\noindent Our proof of the inclusion \af{Mod} (\af{Th} (V 𝒦)) \aof{⊆}
\af{V} \ab{𝒦} proceeds according to the following plan.

\begin{enumerate}
\item \label{item:1} Prove \aof{𝔽[ \ab{X} ]} \af{∈} \af{S} (\af{P} \ab{𝒦}).
\begin{enumerate}
\item \label{item:1.1} Let \ab{𝑪} be the product of all algebras in \af{S} \ab{𝒦}, so \ab{𝑪} \af{∈} \af{P} (\af{S} \ab{𝒦}).
\item \label{item:1.2} Prove \af{P} (\af{S} \ab{𝒦}) \af{⊆} \af{S} (\af{P} \ab{𝒦}), so \ab{𝑪} \af{∈} \af{S} (\af{P} \ab{𝒦}).
\item \label{item:1.3} Prove \aof{𝔽[ \ab{X} ]} \af{≤} \ab{𝑪}, so \aof{𝔽[ \ab{X} ]} \af{∈} \af{S} (\af{S} (\af{P} \ab{𝒦})) (= \af{S} (\af{P} \ab{𝒦})).
\end{enumerate}
\item \label{item:2} Prove that every algebra in \af{Mod} (\af{Th} (V 𝒦)) is a homomorphic image of
\aof{𝔽[ \ab{X} ]}.
\end{enumerate}
From \ref{item:1} and \ref{item:2} will follow \af{Mod} (\af{Th} (V 𝒦))
⊆ \af{H} (\af{S} (\af{P} \ab{𝒦})) (= \af{V} \ab{𝒦}), as desired.

\begin{itemize}
\item
\noindent \ref{item:1.1}. To define \ab{𝑪} as the product of all algebras in \af{S} \ab{𝒦}, we must first contrive
an index type for the class \af{S} \ab{𝒦}.  We do so by letting the indices be the algebras
belonging to \ab{𝒦}. Actually, each index will consist of a triple (\ab{𝑨} , \ab p ,
\ab{ρ}) where \ab{𝑨} is an algebra, \ab p : \ab{𝑨} \af{∈} \af{S} \ab{𝒦} is a proof of membership in \ab{𝒦},
and \ab{ρ} : \ab X \as{→} \aof{𝕌[ \ab{𝑨} ]} is an arbitrary environment.
Using this indexing scheme, we construct \ab{𝑪}, the product of all algebras in \ab{𝒦}
and all environments.

The indexing type \ab{ℑ}, the family of algebras \ab{𝔄}, and the product \ab{𝑪} are defined
as follows.

\ifshort\else

\begin{code}

 open FreeHom {ℓ = ℓ} {𝒦}
 open FreeAlgebra {χ = c}(Th 𝒦)  using ( 𝔽[_] )
 open Environment                using ( Env )
\end{code}
\fi
\begin{code}

 ℑ : Type ι
 ℑ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄 : ℑ → Algebra α ρᵃ
 𝔄 i = ∣ i ∣

 𝑪 : Algebra ι ι
 𝑪 = ⨅ 𝔄

\end{code}
\ifshort\else
\begin{code}
 skEqual : (i : ℑ) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where open Setoid 𝔻[ 𝔄 i ] using ( _≈_ ) ; open Environment (𝔄 i) using ( ⟦_⟧ )

\end{code}

The type \af{skEqual} provides a term identity \ab p \af{≈} \ab q for each index \ab i = (\ab{𝑨} , \ab{p} , \ab{ρ}) of the product.
%(here, as above, \ab{𝑨} is an algebra, \ab{sA} is a proof that \ab{𝑨} belongs to \af{S} \ab{𝒦}, and \ab{ρ} is an environment).
%map assigning values in the domain of \ab{𝑨} to variable symbols in \ab X).
Later we prove that if the identity \ab{p} \af{≈} \ab q holds in all \ab{𝑨} \aof{∈} \af S \ab{𝒦} (for all environments), then \ab p \af{≈} \ab q
holds in the relatively free algebra \Free{X}; equivalently, the pair (\ab p , \ab q) belongs to the
kernel of the natural homomorphism from \T{X} onto \Free{X}. We will use that fact to prove
that the kernel of the natural hom from \T{X} to \ab{𝑪} is contained in the kernel of the natural hom from \T{X} onto \Free{X},
whence we construct a monomorphism from \Free{X} into \ab{𝑪}, and thus \Free{X} is a subalgebra of \ab{𝑪},
so belongs to \af S (\af P \ab{𝒦}).

\fi

\item \noindent \ref{item:1.2}. We need to show that a product of subalgebras of algebras in a class is a subalgebra of a product of algebras in the class;
in other terms, \af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}), for every class \ab{𝒦}.
% We need \af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P}
% \ab{𝒦}) for every class \ab{𝒦},.
\ifshort
The \agdaalgebras library denotes this fact by \af{PS⊆SP}.
As the proof is a bit tedious, it doesn't seem helpful to reproduce it here (\seeshort).
\else
We state and prove this in \agda as follows.

\begin{code}

 private a = α ⊔ ρᵃ ; oaℓ = ov (a ⊔ ℓ)

 PS⊆SP : P (a ⊔ ℓ) oaℓ (S{β = α}{ρᵃ} ℓ 𝒦) ⊆ S oaℓ (P ℓ oaℓ 𝒦)
 PS⊆SP {𝑩} (I , ( 𝒜 , sA , B≅⨅A )) = Goal
  where
  ℬ : I → Algebra α ρᵃ
  ℬ i = ∣ sA i ∣
  kB : (i : I) → ℬ i ∈ 𝒦
  kB i =  fst ∥ sA i ∥
  ⨅A≤⨅B : ⨅ 𝒜 ≤ ⨅ ℬ
  ⨅A≤⨅B = ⨅-≤ λ i → snd ∥ sA i ∥
  Goal : 𝑩 ∈ S{β = oaℓ}{oaℓ}oaℓ (P {β = oaℓ}{oaℓ} ℓ oaℓ 𝒦)
  Goal = ⨅ ℬ , (I , (ℬ , (kB , ≅-refl))) , (≅-trans-≤ B≅⨅A ⨅A≤⨅B)

\end{code}
\fi

\item \noindent \ref{item:1.3}. To prove \aof{𝔽[ \ab{X} ]} \af{≤} \ab{𝑪}, we construct homomorphisms from \ab{𝑻} \ab{X} to \ab{𝑪} and \Free{X} to \ab{𝑪}, the latter of which requires the kernel condition mentioned above.

\begin{code}

 homC : hom (𝑻 X) 𝑪
 homC = ⨅-hom-co 𝔄 (λ i → lift-hom (snd ∥ i ∥))

 kerF⊆kerC : ker ∣ homF[ X ] ∣ ⊆ ker ∣ homC ∣
 kerF⊆kerC {p , q} pKq (𝑨 , sA , ρ) = begin
   free-lift ρ p   ≈˘⟨ free-lift-interp {𝑨 = 𝑨} ρ p ⟩
   ⟦ p ⟧ ⟨$⟩ ρ      ≈⟨ S-id1 {ℓ = ℓ} {p = p} {q} (ζ pKq) 𝑨 sA ρ ⟩
   ⟦ q ⟧ ⟨$⟩ ρ      ≈⟨ free-lift-interp {𝑨 = 𝑨} ρ q ⟩
   free-lift ρ q   ∎
  where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open SetoidReasoning 𝔻[ 𝑨 ]
  open Environment 𝑨  using ( ⟦_⟧ )

  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨

 homFC : hom 𝔽[ X ] 𝑪
 homFC = ∣ HomFactor 𝑪 homC homF[ X ] kerF⊆kerC (isSurjective ∥ epiF[ X ] ∥) ∣

\end{code}
If \AgdaPair{p}{q} belongs to the kernel of \af{homC}, then
\af{Th} \ab{𝒦} includes the identity \ab{p} \af{≈} \ab{q}.
%---that is, \af{Th} \ab{𝒦} \af{⊢} \ab X \af{▹} \ab{p} \af{≈} \ab{q}.
Equivalently,
the kernel of \af{homC} is contained in that of \af{homF[ X ]}.
\ifshort
We omit the proof of this lemma and merely display its formal statement.
\else
\fi

\begin{code}

 kerC⊆kerF : ∀{p q} → (p , q) ∈ ker ∣ homC ∣ → (p , q) ∈ ker ∣ homF[ X ] ∣
\end{code}
\ifshort
\vskip2mm
\else
\begin{code}
 kerC⊆kerF {p}{q} pKq = S𝒦⊫→ker𝔽 (S𝒦⊫ pqEqual)
  where
  S𝒦⊫ : (∀ i → skEqual i {p}{q}) → S{β = α}{ρᵃ} ℓ 𝒦 ⊫ p ≈ q
  S𝒦⊫ x 𝑨 sA ρ = x (𝑨 , sA , ρ)
  S𝒦⊫→ker𝔽 : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ p ≈ q → (p , q) ∈ ker ∣ homF[ X ] ∣
  S𝒦⊫→ker𝔽 x = hyp (S-id2{ℓ = ℓ}{p = p}{q} x)

  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄 i)  using ( ⟦_⟧ )
   open Setoid 𝔻[ 𝔄 i ]    using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
   goal  = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
         ( trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))

\end{code}
\fi
\noindent We conclude that the homomorphism from \Free{X} to \af{𝑪} is injective, whence
\Free{X} is (isomorphic to) a subalgebra of \af{𝑪}.\footnote{The function \af{mon→≤} in
the proof of \af{F≤C} merely extracts a subalgebra witness from a monomorphism.}

\begin{code}

 monFC : mon 𝔽[ X ] 𝑪
 monFC = ∣ homFC ∣ , record { isHom = ∥ homFC ∥ ; isInjective = kerC⊆kerF }

 F≤C : 𝔽[ X ] ≤ 𝑪
 F≤C = mon→≤ monFC

\end{code}
Recall, from \ref{item:1.1} and \ref{item:1.2}, we have \ab{𝑪} \af{∈}
\af{P} (\af{S} \ab{𝒦}) \af{⊆} \af{S} (\af{P} \ab{𝒦}). We now use this, along with
what we just proved (\af{F≤C}), to conclude that \Free{X} belongs to \af{S}
(\af{P} \ab{𝒦}).
\begin{code}

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = let (alg , ∈𝒦 , ≤SP) = PS⊆SP psC in
       (alg , ∈𝒦 , ≤-transitive F≤C ≤SP)
  where
  psC : 𝑪 ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  psC = ℑ , (𝔄 , ((λ i → fst ∥ i ∥) , ≅-refl))

\end{code}
This completes stage \ref{item:1} of the proof.
\end{itemize}

\begin{itemize}
\item
\noindent \ref{item:2}. We show that every algebra in \af{Mod} (\af{Th} (\af{V}
\ab{𝒦})) is a homomorphic image of \af{𝔽[~\ab{X}~]}, as follows.
\ifshort\else
\begin{code}

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra {χ = c}(Th 𝒦) using ( 𝔽[_] )
\end{code}
\fi
\begin{code}

 Var⇒EqCl : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Var⇒EqCl 𝑨 ModThA = 𝔽[ 𝕌[ 𝑨 ] ] , (spFA , AimgF)
  where
  spFA : 𝔽[ 𝕌[ 𝑨 ] ] ∈ S{ι} ι (P ℓ ι 𝒦)
  spFA = SPF{ℓ = ℓ} 𝒦
  epiFlA : epi 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι)
  epiFlA = F-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})
  φ : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  φ = epi→ontohom 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι) epiFlA
  AimgF : 𝑨 IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  AimgF = ∘-hom ∣ φ ∣ (from Lift-≅), ∘-IsSurjective _ _ ∥ φ ∥(fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

\end{code}
\af{ModTh-closure} and \af{Var⇒EqCl} show that
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) holds for every class \ab{𝒦} of \ab{𝑆}-algebras.
Thus, every variety is an equational class.
\end{itemize}

This completes the formal proof of Birkhoff's variety theorem.

%% -----------------------------------------------------------------------------
\section{Related work}
There have been a number of efforts to formalize parts of universal algebra in
type theory besides ours. The Coq proof assistant, based on the Calculus of
Inductive Constructions, was used by Capretta, in~\cite{Capretta:1999}, and
Spitters and Van der Weegen, in~\cite{Spitters:2011}, to formalized the basics
of universal algebra and some classical algebraic structures.
In~\cite{Gunther:2018} Gunther et al developed what seemed (prior to the \agdaalgebras
library) the most extensive library of formalized universal algebra to date.
Like \agdaalgebras,~\cite{Gunther:2018} is based on dependent type theory, is programmed
in \agda, and goes beyond the basic isomorphism theorems to include some equational logic.
Although their coverage is less extensive than that of \agdaalgebras, Gunther et al do treat
\emph{multi-sorted} algebras, whereas \agdaalgebras is currently limited to single-sorted structures.

As noted by Abel~\cite{Abel:2021}, Amato et al, in \cite{Amato:2021}, have
formalized multi-sorted algebras with finitary operators in UniMath. The restriction to
finitary operations was due to limitations of the UniMath type theory, which does
not have W-types nor user-defined inductive types.
Abel also notes that Lynge and Spitters, in~\cite{Lynge:2019}, formalize multi-sorted
algebras with finitary operators in \emph{Homotopy type theory} (\cite{HoTT}) using
Coq.  HoTT's higher inductive types enable them to define quotients as types, without
the need for setoids.  Lynge and Spitters prove three isomorphism theorems concerning
subalgebras and quotient algebras, but do not formalize universal algebras nor varieties.
Finally, in~\cite{Abel:2021}, Abel gives a new formal proof of the soundness theorem and
Birkhoff's completeness theorem for multi-sorted algebraic structures.

%Some other projects aimed at formalizing mathematics generally, and algebra in particular,
% have developed into very extensive libraries that include definitions, theorems, and proofs
% about algebraic structures, such as groups, rings, modules, etc.  However, the goals of these
% efforts seem to be the formalization of special classical algebraic structures, as opposed
% to the general theory of (universal) algebras. Moreover, the part of universal algebra and
% equational logic formalized in the \agdaalgebras library extends beyond the scope of prior efforts.

%Prior to our work, a constructive version of Birkhoff's theorem was published by
% Carlstr\"om in~\cite{Carlstrom:2008}.  However, the logical foundations of that work is constructive set
% theory and, as far as we know, there was no attempt to formalize it in type theory and verify
% it with a proof assistant.


% \section{Conclusion}

% One positive outcome of this project is further evidence in support of dependent type theory and the \agda language. We have shown that, despite the technical demands they place on the user, these technologies are accessible to universal algebraists who possess sufficient patience and resolve to codify their work in type theory and verify their results with a proof assistant.
