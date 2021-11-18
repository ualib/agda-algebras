\section{Introduction}
The Agda Universal Algebra Library (\agdaalgebras) is a collection of types and programs
(theorems and proofs) formalizing the foundations of universal algebra in dependent type
theory using the \agda programming language and proof assistant.
The agda-algebras library now includes a substantial collection of definitions, theorems, and
proofs from universal algebra and equational logic and as such provides many
examples that exhibit the power of inductive and dependent types for
representing and reasoning about general algebraic and relational structures.

The first major milestone of the \agdaalgebras project is a new formal
proof of \emph{Birkhoff's variety theorem} (also known as the \emph{HSP theorem}), the first version
of which was completed in \href{https://github.com/ualib/ualib.github.io/blob/b968e8af1117fc77700d3a588746cbefbd464835/sandbox/birkhoff-exp-new-new.lagda}{January of 2021}.
To the best of our knowledge, this was the first time Birkhoff's theorem had
been formulated and proved in dependent type theory and verified with a proof
assistant.

In this paper, we present a single Agda module called \ualmodule{Demos.HSP}.
This module extracts only those parts of the library needed to prove
Birkhoff's variety theorem. In order to meet page limit guidelines, and to
reduce strain on the reader, we omit proofs of some routine or technical
lemmas that do not provide much insight into the overall development.
However, a long version of this paper, which includes all code in the
\DemosHSP module, is available on the arXiv. [reference needed]

In the course of our exposition of the proof of the HSP theorem, we discuss some of the
more challenging aspects of formalizing \emph{universal algebra} in type theory and the
issues that arise when attempting to constructively prove some of the basic
results in this area.  We demonstrate that dependent type theory and Agda,
despite the demands they place on the user, are accessible to working
mathematicians who have sufficient patience and a strong enough desire to
constructively codify their work and formally verify the correctness of their
results.  Perhpas our presentation will be viewed as a sobering glimpse of the
painstaking process of doing mathematics in the languages of dependent type theory
using the Agda proof assistant. Nonetheless we hope to make a compelling case for
investing in these technologies. Indeed, we are excited to share the gratifying
rewards that come with some mastery of type theory and interactive theorem proving.

%% -----------------------------------------------------------------------------
\subsection{Prior art}
There have been a number of efforts to formalize parts of universal algebra in
type theory prior to ours, most notably

\begin{enumerate}
\item
In~\cite{Capretta:1999}, Capretta formalized the basics of universal algebra in the
   Calculus of Inductive Constructions using the Coq proof assistant;
\item In~\cite{Spitters:2011}, Spitters and van der Weegen formalized the basics of universal algebra
   and some classical algebraic structures, also in the Calculus of Inductive Constructions using
   the Coq proof assistant and promoting the use of type classes;
\item In~\cite{Gunther:2018} Gunther, et al developed what was (prior to the \agdaalgebras library)
   the most extensive library of formalized universal algebra to date; like \agdaalgebras, that work is based on dependent type theory, is programmed in Agda, and goes beyond the Noether isomorphism theorems to include some basic equational logic; although the coverage is less extensive than that of \agdaalgebras, Gunther et al do treat \emph{multisorted} algebras, whereas \agdaalgebras is currently limited to single sorted structures.
\item Lynge and Spitters [@Lynge:2019] (2019) formalize basic, mutisorted universal algebra, up to the
   Noether isomorphism theorems, in homotopy type theory; in this setting, the authors can avoid using
   setoids by postulating a strong extensionality axiom called \textit{univalence}.
\end{enumerate}

Some other projects aimed at formalizing mathematics generally, and algebra in particular, have developed into very extensive libraries that include definitions, theorems, and proofs about algebraic structures, such as groups, rings, modules, etc.  However, the goals of these efforts seem to be the formalization of special classical algebraic structures, as opposed to the general theory of (universal) algebras. Moreover, the part of universal algebra and equational logic formalized in the \agdaalgebras library extends beyond the scope of prior efforts.

% After completing the formal proof in \agda, we learned about a constructive version of Birkhoff's theorem proved by Carlstr\"om in~\cite{Carlstrom:2008}.  The latter is presented in the informal style of standard mathematical writing, and as far as we know it was never formalized in type theory and type-checked with a proof assistant. Nonetheless, a comparison of Carlstr\"om's proof and the \ualib proof would be interesting.




% <!-- ----------------------------------------------------------------------------------- -->

\section{Preliminaries}

\subsection{Logical foundations}

An Agda program typically begins by setting some language options and by
importing types from existing Agda libraries. The language options are specified
using the \ak{OPTIONS} \emph{pragma} which affect control the way Agda behaves by controlling
the deduction rules that are available to us and the logical axioms 
that are assumed when the program is type-checked by Agda to verify its
correctness. Every Agda program in the agda-algebras library, including the
present module (\DemosHSP), begins with the following line.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}
We give only very terse descriptions of these options, and refer the reader to
the accompanying links for more details.

\begin{itemize}
\item
\AgdaPragma{without-K} disables \href{https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29}{Streicher's K axiom}.
See the \href{https://agda.readthedocs.io/en/v2.6.1/language/without-k.html}{section on axiom K} in the \href{https://agda.readthedocs.io/en/v2.6.1.3/language}{Agda Language Reference Manual}~\cite{agdaref-axiomk}.

\item
\AgdaPragma{exact-split} makes Agda accept only those definitions that behave like so-called {\it judgmental} equalities.
See the \href{https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#pattern-matching-and-equality}%
{Pattern matching and equality} section of the \href{https://agda.readthedocs.io/en/v2.6.1.3/tools/}{Agda Tools} documentation~\cite{agdatools-patternmatching}.

\item
\AgdaPragma{safe} ensures that nothing is postulated outright---every non-MLTT axiom has to be an explicit assumption (e.g., an argument to a function or module).
See the \href{https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html#cmdoption-safe}{cmdoption-safe}
section of the \href{https://agda.readthedocs.io/en/v2.6.1.3/tools/}{Agda Tools documentation} and the \href{https://agda.readthedocs.io/en/v2.6.1/language/safe-agda.html#safe-agda}{Safe Agda section} of the \href{https://agda.readthedocs.io/en/v2.6.1.3/language}{Agda Language Reference}~\cite{agdaref-safeagda}.
\end{itemize}


The \AgdaKeyword{OPTIONS} pragma is usually followed by the start of a module and a list of import directives.
For example, the collection of imports required for the present module, \DemosHSP, is relatively modest and appears below.

\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
\begin{code}

-- Import 3 definitions from the agda-algebras library.
open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )
\end{code}
\begin{code}[hide]
module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where
\end{code}
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

-- Assign handles to 3 modules of the Agda Standard Library.
import       Function.Definitions                   as FD
import       Relation.Binary.PropositionalEquality  as ≡
import       Relation.Binary.Reasoning.Setoid       as SetoidReasoning

\end{code}
\ifshort\else
\begin{code}
private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
 𝑓 : fst 𝑆
\end{code}
\fi
Note that the above imports include some of the minor adjustments to ``standard Agda'' syntax to suite our own taste. Take special note of the following conventions used throughout the \agdaalgebras library and this paper: we use \AgdaPrimitive{Type} in place of \AgdaPrimitive{Set}, the infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, instead of \AgdaRecord{Func} (the type of ``setoid functions'' discussed in §\ref{setoid-functions} below), and the symbol \aofld{\au{}⟨\$⟩\au{}} in place of \afld{f} (application of the map of a setoid function); we use
\AgdaField{fst} and \AgdaField{snd}, and sometimes \AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}}, to denote the first and second projections out of the product type \AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}.
\begin{code}[hide]
module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}

%% -----------------------------------------------------------------------------
\subsection{Setoids}
\label{setoids}
A \defn{setoid} is a pair (\ab A, \af{≈}) where \ab A is a type and \af{≈}
is an equivalence relation on \ab A. Setoids seem to have gotten a bad wrap
in some parts of the interactive theorem proving community because of the extra
overhead that their use requires. However, we feel they are ideally suited to
the task of representing the basic objects of informal mathematics (i.e., sets)
in a constructive, type-theoretic way.

A set used informally typically comes equipped with an equivalence relation manifesting
the notion of equality of elements of the set. When working informally, we
often take the equivalence for granted or view it as self-evident; rarely do we
take the time to define it explicitly. While this approach is well-suited to informal
mathematics, formalization using a machine demands that we make nearly everything
explicit, including notions of equality.

Actually, the \agdaalgebras library was first developed without setoids, relying exclusively
on the inductively defined equality type \ad{\au{}≡\au{}} from \am{Agda.Builtin.Equality},
along with some experimental, domain-specific types for equivalence classes, quotients, etc.
One notable consequence of this design decision was that our formalization of many
theorem required postulating function extensionality, an axiom that is not provable
in pure Martin-Löf type theory (MLTT). [reference needed]

In contrast, our current approach using setoids makes the equality relation
of a given type explicit.  A primary motivation for taking this approach is to make it
clear that the library is fully constructive and confined to pure Martin-Löf dependent type theory
(as defined, e.g., in [ref needed]). In particular, there are no appeals to function extensionality in the present work. Finally, we are confident that the current version\footnote{[ref. with version information needed]}  of the \agdaalgebras library is free of hidden assumptions or inconsistencies that could be
used to ``fool'' the type-checker.


%% -----------------------------------------------------------------------------
\subsection{Setoid functions}
\label{setoid-functions}
In addition to the \ar{Setoid} type, much of our code employs the
standard library's \ar{Func} type which represents a function from one
setoid to another and packages such a function with a proof (called \afld{cong}) that
the function respects the underlying setoid equalities. As mentioned above, we renamed
\ar{Func} to the more visually appealing infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, and  throughout the paper we
refer to inhabitants of this type as ``setoid functions.''

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

\paragraph*{Inverses of setoid functions}
We begin by defining an inductive type that represents the semantic concept of the \emph{image} of a function.\footnote{cf.~the \ualmodule{Overture.Func.Inverses} module of the \agdaalgebras library.}

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b

\end{code}
An inhabitant of \aod{Image} \ab f \aod{∋} \ab b is a dependent pair \AgdaPair{a}{p},
where \AgdaTyped{a}{A} and \ab p~\as :~\ab b \af{≈} \ab f~\ab a is a proof that
\ab f maps \ab a to \ab b.  Since the proof that \ab b
belongs to the image of \ab f is always accompanied by a witness \AgdaTyped{a}{A}, we can
actually \emph{compute} a range-restricted right-inverse of \ab f. For convenience, we define this
inverse function and give it the name \af{Inv}.

\begin{code}

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

\end{code}
For each \ab b : \afld{B}, given a pair \AgdaPair{a}{p}~\as :~\aod{Image}~\ab f~\aod{∋}~\ab b witnessing the fact that \ab b belongs to the image of \ab f, the function \af{Inv} simply returns the witness \ab a, which is a preimage of \ab b under \ab f.
We can formally verify that \af{Inv} \ab f is indeed the (range-restricted) right-inverse of \ab f, as follows.

\begin{code}

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p

\end{code}


\paragraph*{Injective and surjective setoid functions}
If \ab{f} % : \ab{𝑨} \aor{⟶} \ab{𝑩}
is a setoid function from % \ab{𝑨} =
(\ab A, \af{≈₀}) to
% \ab{𝑩} =
(\ab B, \af{≈₁}), then we call \ab f \defn{injective} provided
\as{∀} (\ab{a₀} \ab{a₁} \as : \ab{A}), \ab{f} \aofld{⟨\$⟩} \ab{a₀} \af{≈₁} \ab{f} \aofld{⟨\$⟩} \ab{a₁}
implies \ab{a₀} \af{≈₀} \ab{a₁}; we call \ab{f} \defn{surjective} provided
\as{∀} (\AgdaTyped{b}{B}), \as{∃}~(\AgdaTyped{a}{A}) such that \ab{f} \aofld{⟨\$⟩} \ab{a} \af{≈₁} \ab{b}.
The \agdastdlib represents injective functions on bare types by the
type \af{Injective}, and uses this to define the \af{IsInjective} type to represent
the property of being an injective setoid function. Similarly, the type \af{IsSurjective}
represents the property of being a surjective setoid function. \af{SurjInv} represents the \emph{right-inverse} of a surjective function.
         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
 We omit the relatively straightforward formal definitions of these types, but \seeunabridged, as well as formal proofs of some of their properties.
         %%%
\else    %%% END SHORT VERSION ONLY
         %%% BEGIN LONG VERSION ONLY SECTION
         %%%
 We reproduce the definitions and prove some of their properties
 inside the next submodule where we first set the stage by declaring two
 setoids \ab{𝑨} and \ab{𝑩}, naming their equality relations, and making some
 definitions from the standard library available.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑨 using () renaming ( _≈_ to _≈₁_ )
 open Setoid 𝑩 using () renaming ( _≈_ to _≈₂_ )
 open FD _≈₁_ _≈₂_

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
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

\paragraph*{Kernels of setoid functions}
The \defn{kernel} of a function \ab f~\as :~\ab A~\as{→}~\ab B (where \ab A and \ab B are bare types) is defined
informally by \{\AgdaPair{x}{y} \aod{∈} \ab A \aof{×} \ab A \as : \ab f \ab x \as{=} \ab f \ab y \}.
This can be represented in Agda in a number of ways, but for our purposes it is most
convenient to define the kernel as an inhabitant of a (unary) predicate over the square of
the function's domain, as follows.

\begin{code}

kernel : {A : Type α}{B : Type β} → Rel B ρ → (A → B) → Pred (A × A) ρ
kernel _≈_ f (x , y) = f x ≈ f y

\end{code}
The kernel of a \emph{setoid} function \ab f \as : \ab{𝐴} \aor{⟶} \ab{𝐵} is \{\AgdaPair{x}{y} \as{∈} \ab A \aof{×} \ab A \as : \ab f \aofld{⟨\$⟩} \ab x \aofld{≈} \ab f \aofld{⟨\$⟩} \ab y\},
where \afld{\au{}≈\au} denotes equality in \ab{𝐵}. This can be formalized in Agda as follows.

\begin{code}

module _ {𝐴 : Setoid α ρᵃ}{𝐵 : Setoid β ρᵇ} where
 open Setoid 𝐴 using () renaming ( Carrier to A )

 ker : (𝐴 ⟶ 𝐵) → Pred (A × A) ρᵇ
 ker g (x , y) = g ⟨$⟩ x ≈ g ⟨$⟩ y where open Setoid 𝐵 using ( _≈_ )
\end{code}


%% -------------------------------------------------------------------------------------

\section{Types for Basic Universal Algebra}
\label{types-for-basic-universal-algebra}
In this section we develop a working vocabulary and formal types for classical,
single-sorted, set-based universal algebra.
We cover a number of important concepts, but we limit ourselves to those
concepts required in our formal proof of Birkhoff's HSP theorem.
In each case, we give a type-theoretic version of the informal definition,
followed by a formal implementation of the definition in Martin-Löf dependent
type theory using the Agda language.

This section is organized into the following subsections:
§\ref{signatures} defines a general notion of \emph{signature} of a structure and then defines a type that represent signatures;
§\ref{algebras} does the same for \emph{algebraic structures} and \emph{product algebras};
§\ref{homomorphisms} defines \emph{homomorphisms}, \emph{monomorphisms}, and \emph{epimorphisms}, presents types that codify these concepts and formally verifies some of their basic properties;
§§\ref{subalgebras}--\ref{terms} do the same for \emph{subalgebras} and \emph{terms}, respectively.


%% -----------------------------------------------------------------------------
\subsection{Signatures}
\label{signatures}

In model theory, the \defn{signature} \ab{𝑆} = (\ab{𝐶}, \ab{𝐹}, \ab{𝑅}, \ab{ρ})
of a structure consists of three (possibly empty) sets \ab{𝐶}, \ab{𝐹}, and
\ab{𝑅}---called \emph{constant}, \emph{function}, and
\emph{relation} symbols, respectively---along with a function \ab{ρ} : \ab{𝐶} \as{+}
\ab{𝐹} \as{+} \ab{𝑅} \as{→} \ab{𝑁} that assigns an \emph{arity} to each symbol. Often, but
not always, \ab{𝑁} is taken to be the set of natural numbers.

As our focus here is universal algebra, we are more concerned with the
restricted notion of an \defn{algebraic signature}, that is, a signature for
``purely algebraic'' structures, by which is meant a pair \ab{𝑆} = \AgdaPair{F}{ρ}
consisting of a collection \ab{F} of \defn{operation symbols} and an \defn{arity function}
\ab{ρ} : \ab{F} \as{→} \ab{N} which maps each operation symbol to its arity.
Here, \ab{𝑁} denotes the \emph{arity type}. Heuristically, the arity
\ab{ρ} \ab{f} of an operation symbol \ab{f} \as{∈} \ab{F} may be thought of as
the number of arguments that \ab{f} takes as ``input.''

The \agdaalgebras library represents an (algebraic) signature as an
inhabitant of the following dependent pair type:

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

Using special syntax for the first and second
projections---\AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}} (resp.)---if
\ab{𝑆} \as{:} \af{Signature} \ab{𝓞} \ab{𝓥} is a signature, then
\aof{∣} \ab{𝑆} \aof{∣} denotes the set of operation symbols and \aof{∥} \ab{𝑆} \aof{∥} denotes the arity function.
Thus, if \ab{f} \as{:} \aof{∣} \ab{𝑆} \aof{∣} is an operation symbol in the
signature \ab{𝑆}, then \aof{∥} \ab{𝑆} \aof{∥} \ab{f} is the arity of \ab{f}.

We need to augment the ordinary \af{Signature} type so that it supports algebras over setoid domains.
To do so, we follow Andreas Abel's lead [ref needed] and define an operator that translates an
ordinary signature into a \defn{setoid signature}, that is, a signature over a setoid
domain. This raises a minor technical issue concerning the dependent types
involved in the definition; some readers might find the resolution of this issue instructive, so let's discuss it.

Suppose we are given two operations \ab{f} and \ab{g}, a tuple \ab{u} \as{:} \aof{∥} \ab{𝑆} \aof{∥} \ab{f} \as{→}
\ab{A} of arguments for \ab{f}, and a tuple \ab{v} \as{:} \aof{∥} \ab{𝑆}
\aof{∥} \ab{g} \as{→} \ab{A} of arguments for \ab{g}.  If we know that \ab f is identically equal to
\ab{g}---that is, \ab{f} \aod{≡} \ab{g} (intensionally)---then we should be able to
check whether \ab u and \ab v are pointwise equal.  Technically, though, \ab{u} and \ab{v} inhabit different types, so, before comparing them,
we must first convince Agda that \ab u and \ab v inhabit the same type. Of course,
this requires an appeal to the hypothesis \ab f \aod{≡} \ab g, as we see in the definition of \af{EqArgs} below
(adapted from Andreas Abel's development [ref needed]), which neatly resolves this minor technicality.

\begin{code}

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)

EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

\end{code}

Finally, we are ready to define an operator which
translates an ordinary (algebraic) signature into a signature of algebras over setoids.
We denote this operator by \aof{⟨\AgdaUnderscore{}⟩} and define it as follows.

\begin{code}

⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

Carrier  (⟨ 𝑆 ⟩ ξ)                = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)
_≈ˢ_     (⟨ 𝑆 ⟩ ξ)(f , u)(g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

reflᵉ   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → reflˢ   ξ
symᵉ    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → symˢ    ξ (g i)
transᵉ  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → transˢ  ξ (g i) (h i)
\end{code}

%% -----------------------------------------------------------------------------
\subsection{Algebras}
\label{algebras}
Informally, an \defn{algebraic structure in the signature} \ab{𝑆} = (\ab{F}, \ab{ρ}) (or \ab{𝑆}-\defn{algebra}) is denoted by \ab{𝑨} = (\ab{A}, \ab{Fᴬ}) and consists of
\begin{itemize}
\item a \emph{nonempty} set (or type) \ab A, called the \emph{domain} of the algebra;
\item a collection \ab{Fᴬ} := \{ \ab{fᴬ} \as{∣} \ab f \as{∈} \ab F, \ab{fᴬ} \as : (\ab{ρ} \ab f \as{→} \ab A) \as{→} \ab A \} of \emph{operations} on \ab{A};
\item a (potentially empty) collection of \emph{identities} satisfied by elements and operations of \ab{𝑨}.
\end{itemize}
The \agdaalgebras library represents algebras as the inhabitants of a record type with two fields:
\begin{itemize}
\item \afld{Domain}, representing the domain of the algebra;
\item \afld{Interp}, representing the \emph{interpretation} in the algebra of each operation symbol in \ab{𝑆}.
\end{itemize}
The \afld{Domain} is a actually a setoid whose \afld{Carrier} denotes the carrier of the algebra and whose equivalence relation denotes equality of elements of the domain.

Here is the definition of the \ar{Algebra} type followed by an explaination of how the standard library's \ar{Func} type is used to represent the interpretation of operation symbols in an algebra.
%\footnote{We postpone introducing identities until they are needed (e.g., for equational logic); see~§\ref{model-theory-and-equational-logic}.}

\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain

\end{code}
Recall, we renamed Agda's \ar{Func} type, prefering instead the long-arrow symbol \AgdaRecord{⟶}, so
the \afld{Interp} field has type \ar{Func} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain}) \afld{Domain}, a record type with two fields:
\begin{itemize}
\item a function  \ab{f} \as : \afld{Carrier} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain})
  \as{→} \afld{Carrier} \afld{Domain} representing the operation;
\item a proof \af{cong} \as : \ab f \aof{Preserves \au{}≈₁\au{} ⟶ \au{}≈₂\au{}} that the operation preserves the relevant setoid equalities.
\end{itemize}
Thus, for each operation symbol in the signature \ab{𝑆}, we have a setoid function \ab f---with domain a power of \afld{Domain} and codomain \afld{Domain}---along with a proof that this function respects the setoid equalities.  The latter means that the operation \ab{f} is accompanied by a proof of the following: ∀ \ab u \ab v in \afld{Carrier} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain}), if \ab u \af{≈₁} \ab v, then \ab{f} \aofld{⟨\$⟩} \ab{u} \af{≈₂} \ab{f} \aofld{⟨\$⟩} \ab{v}.

In the \agdaalgebras library is defined some syntactic sugar that helps to make our formalizations easier to read and
comprehend.
%\footnote{We omit the formal definitions, but see [reference needed].}
The following are three examples of such syntax that we use below: if \ab{𝑨} is an algebra, then
\begin{itemize}
\item \aof{𝔻[ \ab{𝑨} ]} denotes the setoid \afld{Domain} \ab{𝑨},
\item \aof{𝕌[ \ab{𝑨} ]} is the underlying carrier of the algebra \ab{𝑨}, and
\item \ab f \aof{̂} \ab{𝑨} denotes the interpretation in the algebra \ab{𝑨} of the operation symbol \ab f.
\end{itemize}
         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
 We omit the straightforward formal definitions of these types, but \seeunabridged.
         %%%
\else    %%% END SHORT VERSION ONLY
         %%% BEGIN LONG VERSION ONLY SECTION
         %%%
\begin{code}
open Algebra
𝔻[_] : Algebra α ρᵃ →  Setoid α ρᵃ
𝔻[ 𝑨 ] = Domain 𝑨
𝕌[_] : Algebra α ρᵃ →  Type α
𝕌[ 𝑨 ] = Carrier (Domain 𝑨)
_̂_ : (f : ∣ 𝑆 ∣)(𝑨 : Algebra α ρᵃ) → (∥ 𝑆 ∥ f  →  𝕌[ 𝑨 ]) → 𝕌[ 𝑨 ]
f ̂ 𝑨 = λ a → (Interp 𝑨) ⟨$⟩ (f , a)
\end{code}

%% -----------------------------------------------------------------------------
\paragraph*{Universe levels of algebra types}
%\paragraph*{Agda's universe hierarchy}\label{agdas-universe-hierarchy}
The hierarchy of type universes in Agda is structured as follows:
\ap{Type} \ab{ℓ} : \ap{Type} (\ap{lsuc} \ab{ℓ}), \ap{Type} (\ap{lsuc} \ab{ℓ}) : \ap{Type} (\ap{lsuc} (\ap{lsuc} \ab{ℓ})), ….
This means that \ap{Type} \ab{ℓ} has type \ap{Type} (\ap{lsuc} \ab{ℓ}), etc.  However, this does \emph{not} imply that
\ap{Type} \ab{ℓ} : \ap{Type} (\ap{lsuc} (\ap{lsuc} \ab{ℓ})). In other words, Agda's universe hierarchy is \emph{noncumulative}.
This can be advantageous as it becomes possible to treat universe levels more generally and precisely. On the other hand,
an unfortunate side-effect of this noncumulativity is that it sometimes seems unduly difficult to convince Agda that a program
or proof is correct.

This aspect of the language was one of the few stumbling blocks we encountered while learning how to use Agda for formalizing universal algebra in type theory.
Although some may consider this to be one of the least interesting and most annoying aspects of our work, others might find
this presentation most helpful if we resist the urge to gloss over the more technical and less elegant aspects of the library.
Therefore, we will show how to use the general universe lifting and lowering functions, available in the \agdastdlib,
to develop bespoke, domain-specific tools for dealing with the noncumulative universe hierarchy.

%\paragraph*{Lifting and lowering}
Let us be more concrete about what is at issue here by considering a typical example. Agda frequently encounters errors during the type-checking process and responds by printing an error message. Often the message has the following form.
{\color{red}{\small
\begin{verbatim}
  HSP.lagda:498,20-23
  α != 𝓞 ⊔ 𝓥 ⊔ (lsuc α) when checking that... has type...
\end{verbatim}}}
\noindent Here Agda informs us that it encountered universe level \ab{α} on line 498 of the HSP module, where it was expecting level \ab{𝓞}~\aop{⊔}~\ab{𝓥}~\aop{⊔}~(\ap{lsuc} \ab{α}).
For example, we may have tried to use an algebra inhabiting the type \ar{Algebra} \ab{α} \ab{ρᵃ} whereas we should have used one inhabiting the type \ar{Algebra} (\ab{𝓞} \aop{⊔} \ab{𝓥} \aop{⊔} (\ap{lsuc} \ab{α})) \ab{ρᵃ}.
One resolves such problems using the general \AgdaRecord{Lift} record type, available in the standard library, which takes a type inhabiting some universe and embeds it into a higher universe.
To apply this strategy in our domain of interest, we develop the following utility functions.

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


Lift-Alg : (𝑨 : Algebra α ρᵃ)(ℓ₀ ℓ₁ : Level) → Algebra (α ⊔ ℓ₀) (ρᵃ ⊔ ℓ₁)
Lift-Alg 𝑨 ℓ₀ ℓ₁ = Lift-Algʳ (Lift-Algˡ 𝑨 ℓ₀) ℓ₁

\end{code}
To see why these functions are useful, first recall that our definition of the algebra record type uses two universe level parameters corresponding to those of the algebra's underlying domain setoid.
Concretely, an algebra of type \ar{Algebra} \ab{α} \ab{ρᵃ} has a domain setoid (called \afld{Domain}) of type \ar{Setoid} \ab{α} \ab{ρᵃ}. This domain setoid packages a ``carrier set'' (\afld{Carrier}),
inhabiting \ap{Type} \ab{α}, with an equality on \afld{Carrier} of type \af{Rel} \afld{Carrier} \ab{ρᵃ}. Now, examining the \af{Lift-Alg} function, we see that it
takes an algebra---one whose carrier set inhabits \ap{Type \ab{α}} and has an equality of type \af{Rel} \afld{Carrier} \ab{ρᵃ}---and constructs a new algebra with carrier set inhabiting \ap{Type} (\ab{α} \ap{⊔} \ab{ℓ₀}) and having an equality of type \af{Rel} \afld{Carrier} (\ab{ρᵃ} \ap{⊔} \ab{ℓ₁}).
Of course, this lifting operation would be useless if we couldn't establish a connection (beyond universe levels) between the input and output algebras.
Fortunately, we can prove that universe lifting is an \defn{algebraic invariant}, which is to say that the lifted algebra
has the same algebraic properties as the original algebra; more precisely, the input algebra and the lifted algebra are \defn{isomorphic}, as we prove below. (See \af{Lift-≅}.)
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

\paragraph*{Product Algebras}
We give an informal description of the \defn{product} of a family of \ab{𝑆}-algebras and then define a type which formalizes this notion.

Let \ab{ι} be a universe and \ab I~:~\ap{Type}~\ab{ι} a type (which, in the
present context, we might refer to as the ``indexing type'').
Then the dependent function type \ab{𝒜}~:~\ab
I~\as{→}~\ab{Algebra}~\ab{α}~\ab{ρᵃ} represents an \defn{indexed family of algebras}.
Denote by \af{⨅}~\ab{𝒜} the \defn{product of algebras} in \ab{𝒜} (or \defn{product algebra}),
by which we mean the algebra whose domain is the Cartesian product \af{Π}~\ab
i~꞉~\ab I~\af{,}~\aof{𝔻[~\ab{𝒜}~\ab i~]} of the domains of the algebras in
\ab{𝒜}, and whose operations are those arising by point-wise interpretation in the obvious
way: if \ab{f} is a \ab J-ary operation symbol and if \ab a~:~\af{Π}~\ab
i~꞉~\ab I~\af{,}~\ab J~\as{→}~\aof{𝔻[~\ab{𝒜}~\ab i~]} is, for each \ab
i~:~\ab I, a \ab J-tuple of elements of the domain \aof{𝔻[~\ab{𝒜}~\ab i~]}, then
we define the interpretation of \ab f in \af{⨅}~\ab{𝒜} by (\ab{f}~\af{̂}~\af{⨅}~\ab{𝒜}) \ab a := \as{λ}~(\ab i~:~\ab I)~\as{→} (\ab{f}~\af{̂}~\ab{𝒜}~\ab i)(\ab{a}~\ab i).

The \agdaalgebras library defines a function called \af{⨅} which formalizes the foregoing notion of \defn{product algebra} in Martin-Löf type theory.
\ifshort
Here we merely display this function's interface, but see the \ualmodule{Algebras.Func.Products} module for the complete definition.

\else
\fi
\begin{code}

module _ {ι : Level}{I : Type ι } where
 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
\end{code}
\ifshort\else
\begin{code}
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
\fi




%% -------------------------------------------------------------------------------------

\subsection{Homomorphisms}
\label{homomorphisms}

%\paragraph*{Basic definitions}
Suppose \ab{𝑨} and \ab{𝑩} are \ab{𝑆}-algebras. A \defn{homomorphism} (or
``hom'') from \ab{𝑨} to \ab{𝑩} is a setoid function
\ab{h}~:~\aof{𝔻[ \ab{𝑨} ]} \as{→} \aof{𝔻[ \ab{𝑩} ]} that is \defn{compatible}
(or \defn{commutes}) with all basic operations; that is,
for every operation symbol \ab{f}~:~\af{∣ \ab{𝑆} ∣} and all tuples
\ab{a}~:~\af{∥ \ab{𝑆} ∥}~\ab{f} \as{→} \aof{𝔻[ \ab{𝑨} ]}, the following
equality holds: \ab{h} \aofld{⟨\$⟩} (\ab{f}~\af{̂}~\ab{𝑨}) \ab{a} \af{≈}
(\ab{f}~\af{̂}~\ab{𝑩}) \as{λ} \ab{x} \as{→} \ab{h} \aofld{⟨\$⟩} (\ab{a} \ab{x}).

To formalize this concept in Agda, we first define a type \af{compatible-map-op}
representing the assertion that a given setoid function
\ab{h}~:~\aof{𝔻[ \ab{𝑨} ]} \as{→} \aof{𝔻[ \ab{𝑩} ]} commutes with a given
basic operation \ab{f}.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

\end{code}
Generalizing over operation symbols gives the following type of compatible maps
from (the domain of) \ab{𝐴} to (the domain of) \ab{𝑩}.

\begin{code}

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f

\end{code}
With this we define a record type \ar{IsHom} representing the property of being
a homomorphism, and finally the type \af{hom} of homomorphisms from \ab{𝑨} to \ab{𝐵}.
\begin{code}

 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor mkhom ; field compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

\end{code}
Observe that an inhabitant of \af{hom} is a pair (\ab h , \ab p) whose first component is a setoid function from the domain of \ab{𝑨} to that of \ab{𝑩} and whose second component is \ab p : \ar{IsHom} \ab h, a proof that \ab h is a homomorphism.

A \defn{monomorphism} (resp. \defn{epimorphism}) is an injective (resp. surjective) homomorphism.  The \agdaalgebras library defines types \ar{IsMon} and \ar{IsEpi} to represent these properties, as well as
\af{mon} and \af{epi}, the types of monomorphisms and epimorphisms, respectively.
         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
 We won't reproduce the formal definitions of these types here, but \seeunabridged.
         %%%
\else    %%% END SHORT VERSION ONLY
         %%% BEGIN LONG VERSION ONLY SECTION
         %%%
\begin{code}

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h

  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

\end{code}
As with \af{hom}, the type \af{mon} is a dependent product type; each inhabitant is a pair consisting of a setoid function, say, \ab h, along with a proof that \ab h is a monomorphism.

\begin{code}

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h

  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
\end{code}

Here are two mere utilities that are useful for translating between types.

\begin{code}[hide]
open IsHom ; open IsMon ; open IsEpi

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
\end{code}

\paragraph*{Composition of homomorphisms}
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

The composition of homomorphisms is again a homomorphism, and similarly for epimorphisms (and monomorphisms).
\ifshort
The proofs of these facts are relatively straightforward so we omit them. When applied below, they are called \af{∘-hom} and \af{∘-epi}.
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
Here we define the identity homomorphism for setoid algebras. Then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

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
%\label{homomorphisms-of-product-algebras}
Suppose we have an algebra \ab{𝑨}, a type \ab I : \ap{Type} \ab{𝓘}, and a family \ab{ℬ} : \ab I \as{→} \ar{Algebra} \ab{β} \ab{ρᵇ} of algebras.
We sometimes refer to the inhabitants of \ab{I} as \emph{indices}, and call \ab{ℬ} an \defn{indexed family of algebras}. If in addition we have a family \ab{𝒽} : (\ab i : \ab I) → \af{hom} \ab{𝑨} (\ab{ℬ} \ab i) of homomorphisms, then we can construct a homomorphism from \ab{𝑨} to the product \af{⨅} \ab{ℬ} in the natural way.  The latter is codified in dependent type theory by the function \af{⨅-hom-co} defined below.\footnote{cf.~the \ualmodule{Homomorphisms.Func.Products} module of the \agdaalgebras library.}

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
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

Another basic but important fact about homomorphisms is the following factorization theorem: if \ab g : \af{hom} \ab{𝑨} \ab{𝑩}, \ab h : \af{hom} \ab{𝑨} \ab{𝑪}, \ab h is surjective,
and \af{ker} \ab h \aof{⊆} \af{ker} \ab g, then there exists \ab{φ} : \af{hom} \ab{𝑪} \ab{𝑩}
such that \ab g = \ab{φ} \aof{∘} \ab h.  The type \af{HomFactor}, defined below, formalizes this result in MLTT.
         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
Here we merely give a formal statement of this theorem.
%, but \seeunabridged or the\ualmodule{Homomorphisms.Func.Factor} module of the \agdaalgebras library.
         %%%
\else\fi %%% END SHORT VERSION ONLY

\begin{AgdaAlign}
\begin{code}

module _ {𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ){𝑪 : Algebra γ ρᶜ}
         (gh : hom 𝑨 𝑩)(hh : hom 𝑨 𝑪) where
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈₂_ )
 open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈₃_ )
 private gfunc = ∣ gh ∣ ; g = _⟨$⟩_ gfunc ; hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 HomFactor :  kernel _≈₃_ h ⊆ kernel _≈₂_ g
  →           IsSurjective hfunc
  →           Σ[ φ ∈ hom 𝑪 𝑩 ] ∀ a → g a ≈₂ ∣ φ ∣ ⟨$⟩ h a
\end{code}
\ifshort %%%
\else    %%% BEGIN LONG VERSION ONLY
         %%%
\begin{code}
 HomFactor Khg hE = (φmap , φhom) , gφh
  where
  kerpres : ∀ a₀ a₁ → h a₀ ≈₃ h a₁ → g a₀ ≈₂ g a₁
  kerpres a₀ a₁ hyp = Khg hyp

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

\paragraph*{Isomorphisms}
%\label{isomorphisms}
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%
\end{AgdaAlign}

\ifshort \medskip \else \fi

Two structures are \defn{isomorphic} provided there are homomorphisms going back and forth between them which compose to the identity map.
         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
The \agdaalgebras library's \ar{\au{}≅\au{}} type codifies the definition of isomorphism, as well as some obvious consequences.  Here we display only the core part of this record type, but \seeunabridged or the \ualmodule{Homomorphisms.Func.Isomorphisms} module of the \agdaalgebras library.
         %%%
\else    %%% BEGIN LONG VERSION ONLY
         %%%
This notion is formalized in the \agdaalgebras library as the record type \ar{\au{}≅\au{}}, whose definition we present below.  Note that the definition includes statements and proofs of some easy consequences---namely, that the maps back-and-forth are bijective. This makes it easy to apply these facts when they are needed.
\fi %%% END SHORT VERSION ONLY
    %%%
\begin{code}

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ )
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᴮ_ )

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field        to : hom 𝑨 𝑩
               from : hom 𝑩 𝑨
               to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
               from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ a

\end{code}
\ifshort %%%
\else    %%% BEGIN LONG VERSION ONLY
         %%%
\begin{code}
  toIsSurjective : IsSurjective ∣ to ∣
  toIsSurjective {y} = eq (∣ from ∣ ⟨$⟩ y) (sym (to∼from y))
   where open Setoid 𝔻[ 𝑩 ] using ( sym )

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x}{y} xy = trans (sym (from∼to x)) (trans ξ (from∼to y))
   where
   open Setoid 𝔻[ 𝑨 ] using ( sym ; trans )
   ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
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

Fortunately, the lift operation \af{Lift-Alg} that we defined above is an \emph{algebraic invariant}, by which we mean that isomorphism classes of algebras are closed under \af{Lift-Alg}.
As our focus is universal algebra, this crucial property is why we can use the lift operation
to solve the technical problems arising from the noncumulativity of Agda's universe
hierarchy without changing the algebraic semantics.

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})

 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ

\end{code}
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

We conclude this section on homomorphisms with what seems, for our purposes, the most useful way to represent the class of \emph{homomorphic images} of an algebra in dependent type theory.
(The first function, \af{ov}, merely provides a handy shorthand for universe levels.)
%\footnote{cf.~the \ualmodule{Homomorphisms.Func.HomomorphicImages} module of the \agdaalgebras library.}

\begin{code}

ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type _
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}
For future reference we record the fact that an algebra is its own homomorphic image.

\begin{code}

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid (Domain 𝑨) using ( refl )
\end{code}
\ifshort %%%
\else    %%% BEGIN LONG VERSION ONLY
         %%%

\medskip

\noindent These types should be self-explanatory, but just to be sure, we pause
to describe the semantics of the Sigma type appearing in the definition of \af{HomImages}.
If \ab{𝑨} : \af{Algebra} \ab{α} \ab{ρᵃ} is an \ab{𝑆}-algebra, then \af{HomImages} \ab{𝑨}
denotes the type of pairs (\ab{𝑩} \aic{,} \ab p) such that \ab{𝑩} : \ar{Algebra} \ab{β} \ab{ρᵇ}
and \ab p is a proof that there exists a homomorphism from \ab{𝑨} onto \ab{𝑩}.
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

%% -------------------------------------------------------------------------------------

\subsection{Subalgebras}
\label{subalgebras}
%\paragraph*{Basic definitions}
%\label{subalgebras-basic-definitions}
Given \ab{𝑆}-algebras \ab{𝑨} and \ab{𝑩}, we say that \ab{𝑨} is a \defn{subalgebra} of \ab{𝑨} and write
\AgdaBound{𝑨}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{≤}}\AgdaSpace{}%
\AgdaBound{𝑩}
just in case \ab{𝑨} can be \emph{homomorphically embedded} in \ab{𝑩}; in other terms,
\AgdaBound{𝑨}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{≤}}\AgdaSpace{}%
\AgdaBound{𝑩}
iff there exists a monomorphism \ab{h} : \af{mon} \ab{𝑨} \ab{𝑩} from \ab{𝑨} to \ab{𝑩}.

The following definition codifies the binary subalgebra relation
\AgdaOperator{\AgdaFunction{\au{}≤\au{}}} on the class of \ab{𝑆}-algebras in MLTT.

\begin{code}

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
\end{code}

%\paragraph*{Basic properties}
Obviously the subalgebra relation is reflexive by the identity monomorphism, as well as transitive since composition of monomorphisms is a monomorphism.  Here we merely give the formal statements, but omit the easy proofs, of these results.

\begin{code}

≤-reflexive   :  {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨

≤-transitive  :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ}
 →               𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪

\end{code}
\begin{code}[hide]
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id

≤-transitive ( f , finj ) ( g , ginj ) = (∘-hom f g ) , ∘-IsInjective ∣ f ∣ ∣ g ∣ finj ginj
\end{code}

If \ab{𝒜} : \ab I → \af{Algebra} \ab{α} \ab{ρᵃ} and
\ab{ℬ} : \ab I → \af{Algebra} \ab{β} \ab{ρᵇ} are families of \ab{𝑆}-algebras
such that \ab{ℬ} \ab i \af{≤} \ab{𝒜} \ab i for every \ab i : \ab I, then
\af{⨅} \ab{ℬ} is a subalgebra of \af{⨅} \ab{𝒜}.
\ifshort
We omit the straightforward proof and merely assign the formalization of this result the name \af{⨅-≤} for future reference.
\else
\begin{code}
module _ {ι : Level} {I : Type ι}{𝒜 : I → Algebra α ρᵃ}{ℬ : I → Algebra β ρᵇ} where
 ⨅-≤ : (∀ i → ℬ i ≤ 𝒜 i) → ⨅ ℬ ≤ ⨅ 𝒜
 ⨅-≤ B≤A = (hfunc , hhom) , hM
  where
  hi : ∀ i → hom (ℬ i) (𝒜 i)
  hi i = ∣ B≤A i ∣
  hfunc : 𝔻[ ⨅ ℬ ] ⟶ 𝔻[ ⨅ 𝒜 ]
  (hfunc ⟨$⟩ x) i = ∣ hi i ∣ ⟨$⟩ x i
  cong hfunc = λ xy i → cong ∣ hi i ∣ (xy i)
  hhom : IsHom (⨅ ℬ) (⨅ 𝒜) hfunc
  compatible hhom = λ i → compatible ∥ hi i ∥
  hM : IsInjective hfunc
  hM = λ xy i → ∥ B≤A i ∥ (xy i)

\end{code}
\fi
We conclude this brief subsection on subalgebras with two easy facts that will be useful later, when we prove the HSP theorem. The first merely converts a monomorphism into a pair in the subalgebra relation
 while the second is an algebraic invariance property of \AgdaOperator{\AgdaFunction{\au{}≤\au{}}}.
\ifshort
(Proofs omitted.)
\else\fi

\begin{code}

mon→≤      :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩

≅-trans-≤  :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ}
 →            𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
\end{code}
\ifshort\else
\begin{code}
≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-IsInjective ∣ to A≅B ∣ ∣ h ∣ (toIsInjective A≅B) hinj)

mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x
\end{code}
\fi

%% -------------------------------------------------------------------------------------

\subsection{Terms}
\label{terms}
%\paragraph*{Basic definitions}
Fix a signature \ab{𝑆} and let \ab X denote an arbitrary nonempty collection of variable symbols.
(The chosen collection of variable symbols is sometimes called the \defn{context}.)
Assume the symbols in \ab X are distinct from the operation symbols of \ab{𝑆}, that is \ab X \aof{∩} \aof{∣} \ab{𝑆} \aof{∣} = ∅.

A \defn{word} in the language of \ab{𝑆} is a finite sequence of members of \ab X \aof{∪} \aof{∣} \ab{𝑆} \aof{∣}. We denote the concatenation of such sequences by simple juxtaposition.
Let \ab{S₀} denote the set of nullary operation symbols of \ab{𝑆}. We define by induction on \ab n the sets \ab{𝑇ₙ} of \emph{words} over \ab X \aof{∪} \aof{∣} \ab{𝑆} \aof{∣} as follows (cf.~\cite[Def. 4.19]{Bergman:2012}): \ab{𝑇₀} := \ab X \aof{∪} \ab{S₀} and \ab{𝑇ₙ₊₁} := \ab{𝑇ₙ} \aof{∪} \ab{𝒯ₙ},
where \ab{𝒯ₙ} is the collection of all \ab f \ab t such that \ab f : \aof{∣} \ab{𝑆} \aof{∣} and \ab t : \aof{∥} \ab{𝑆} \aof{∥} \ab f \as{→} \ab{𝑇ₙ}. (Recall, \aof{∥} \ab{𝑆} \aof{∥} \ab f is the arity of the operation symbol \ab f.) An \ab{𝑆}-\defn{term} is a term in the language of \ab{𝑆} and the collection of all \ab{𝑆}-\defn{terms} in the context \ab X is given by \ad{Term} \ab X := \aof{⋃ₙ} \ab{𝑇ₙ}.

As even its informal definition of \ad{Term} \ab X is recursive, it should come as no surprise that
the semantics of terms can be faithfully represented in type theory as an inductive type.
Indeed, here is such a representation.

\begin{code}

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X

\end{code}
This is a very basic inductive type that represents each term as a tree with an operation symbol at each \aic{node} and a variable symbol at each leaf (\aic{ℊ}); hence the constructor names (\aic{ℊ} for ``generator'' and \aic{node} for ``node''). We will enrich this type with an inductive type \ad{\au{}≃\au{}} representing equality of terms, and then we will package up \ad{Term}, \ad{\au{}≃\au{}}, and a proof that \ad{\au{}≃\au{}} is an equivalence relation into a setoid of \ab{𝑆}-terms.
Ultimately we will use this term setoid as the domain of an algebra---the (absolutely free) \emph{term algebra} in the signature \ab{𝑆}.

First, the equality-of-terms type is defined as follows.

\begin{code}

module _ {X : Type χ } where

 data _≃_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)

\end{code}
Next, we would show that equality of terms so defined is an equivalence relation, but the proof
of this fact is trivial, so we omit it and merely give the fact a name; call it \af{≃-isEquiv}.

\begin{code}[hide]

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


\paragraph*{The term algebra}
%\label{the-term-algebra}
For a given signature \ab{𝑆}, if the type \ad{Term} \ab X is nonempty
(equivalently, if \ab X or \aof{∣} \ab{𝑆} \aof{∣} is nonempty), then we can
define an algebraic structure, denoted by \T{X} and called the \defn{term
  algebra in the signature} \ab{𝑆} \defn{over} \ab X.  Terms are viewed as
acting on other terms, so both the domain and basic operations of the algebra
are the terms themselves.

For each operation symbol \ab f : \aof{∣} \ab{𝑆} \aof{∣}, we denote by \ab f
\aof{̂} \T{X} the operation on \ad{Term} \ab X that maps each tuple of terms, say, \ab t :
  \aof{∥} \ab{𝑆} \aof{∥} \ab f \as{→} \ad{Term} \ab X, to the formal term \ab f \ab t.
We let \T{X} denote the term algebra
 in \ab{𝑆} over \ab X; it has universe \ad{Term} \ab X and operations \ab f \aof{̂} \T{X}, one for each symbol \ab f in \aof{∣} \ab{𝑆} \aof{∣}. Finally, we formalize this notion of term algebra in \agda as follows.

\begin{code}

TermSetoid : (X : Type χ) → Setoid _ _
TermSetoid X = record { Carrier = Term X ; _≈_ = _≃_ ; isEquivalence = ≃-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≃ts) = gnl ss≃ts
\end{code}

\paragraph*{Environments and the interpretation of terms therein}
In this section, we formalize the notions \emph{environment} and \emph{interpretation of terms} in an algebra, evaluated in an environment. The approach to formalizing these notions, as well as the Agda code presented in this subsection, is based on similar code developed by Andreas Abel to formalize Birkhoff's completeness theorem.\footnote{See \abel.}

\ifshort\else
Recall that the domain of an algebra \ab{𝑨} is a setoid, which we denote by \af{𝔻[ \ab{𝑨} ]}, whose \afld{Carrier} is the universe of the algebra, \af{𝕌[ \ab{𝑨} ]}, and whose equivalence relation represents equality of elements in \af{𝕌[ \ab{𝑨} ]}.
\fi

Fix a signature \ab{𝑆}, a context of variable symbols \ab X, and an \ab{𝑆}-algebra \ab{𝑨}. An \defn{environment} for these data is a function \ab{ρ} : \ab X \as{→} \af{𝕌[ \ab{𝑨} ]} which assigns a value in the universe to each variable symbol in the context.
We represent the notion of environment in Agda using a function, \af{Env}, which takes an algebra \ab{𝑨} and a context \ab{X} and returns a setoid whose \afld{Carrier} has type \ab X \as{→} \af{𝕌[ \ab{𝑨} ]} and whose equivalence relation is pointwise equality of functions in \ab X \as{→} \af{𝕌[ \ab{𝑨} ]} (relative to the setoid equality of \af{𝔻[ \ab{𝑨} ]}).

Before defining the \af{Env} function (which will depend on a specific algebra) we first define a substitution from one context, say, \ab X, to another \ab Y, which assigns a term in \ab X to each symbol in \ab Y.  The definition of \af{Sub} (which does not depend on a specific algebra) is a slight modification of the one given by Andreas Abel (\textit{op.~cit.}), as is the recursive definition of the syntax \ab t \af{[} \ab{σ} \af{]}, which denotes a term \ab t applied to a substitution \ab{σ}.

\begin{code}

Sub : Type χ → Type χ → Type _
Sub X Y = (y : Y) → Term X

_[_] : {X Y : Type χ}(t : Term Y) (σ : Sub X Y) → Term X
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])

\end{code}

Now we are ready to define the aforementioned environment function \af{Env}
as well as the recursive function \af{⟦\au{}⟧} which defines the \defn{interpretation} of a term in a given algebra, \emph{evaluated} in a given environment.  Since the next few definitions are relative to a certain fixed algebra, we put them inside a submodule called \am{Environment} so that later, when we load the environment, we can associate its definitions with different algebras.

\begin{code}

module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ τ → (x : X) → ρ x ≈ τ x
                 ; isEquivalence = record  { refl   = λ _      → refl
                                           ; sym    = λ h x    → sym (h x)
                                           ; trans  = λ g h x  → trans (g x)(h x) }}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v          = u≈v x
 cong ⟦ node f args ⟧ x≈y  = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}

Two terms interpreted in \ab{𝑨} are proclaimed \defn{equal} if they are equal for all environments.  This equivalence of terms%
\ifshort\else
, and proof that it is an equivalence relation,
\fi
 is formalized in Agda as follows.

\begin{code}

 Equal : {X : Type χ}(s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

 ≃→Equal : {X : Type χ}(s t : Term X) → s ≃ t → Equal s t
 ≃→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≃→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≃→Equal(s i)(t i)(x i)ρ )

\end{code}
\ifshort
The proof that \af{Equal} is an equivalence relation is trivial, so we omit it.
\else
\begin{code}
 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 reflᵉ   EqualIsEquiv = λ _        → refl
 symᵉ    EqualIsEquiv = λ x=y ρ    → sym (x=y ρ)
 transᵉ  EqualIsEquiv = λ ij jk ρ  → trans (ij ρ) (jk ρ)

\end{code}
\fi

A substitution from one context \ab X to another \ab Y is used to transport an environment from \ab X to \ab Y and the function \af{⟦\au{}⟧} defined below carries out this transportation of environments.

\begin{code}

 ⟦_⟧s : {X Y : Type χ} → Sub X Y → Carrier(Env X) → Carrier (Env Y)
 ⟦ σ ⟧s ρ x = ⟦ σ x ⟧ ⟨$⟩ ρ

\end{code}

Finally, we have a substitution lemma which says that \aof{⟦} \ab{t} \af{[} \ab{σ} \af{]} \aof{⟧} \aofld{⟨\$⟩} \ab{ρ} (= the term \ab{t} applied to a substitution \ab{σ} and evaluated in an evironment \ab{ρ}) is the same as \aof{⟦ \ab{t} ⟧} \aofld{⟨\$⟩} \aof{⟦ \ab{σ} ⟧s} \ab{ρ} (= the term \ab{t} evaluated in the \ab{σ}-transported environment). %\aof{⟦} \ab{σ} \aof{⟧} \ab{ρ}.

\begin{code}

 substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
  →              ⟦ t [ σ ] ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ⟦ σ ⟧s ρ

 substitution (ℊ x)        σ ρ = refl
 substitution (node f ts)  σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)

\end{code}
This concludes the definition of the \am{Environment} module (based on Abel's Agda proof of the completeness theorem; \textit{op.~cit.}).

\ifshort\else
\paragraph*{Compatibility of terms}
%\label{compatibility-of-terms}
\fi
Later we will need two important facts about term operations.  The first, called \af{comm-hom-term}, asserts that every term commutes with every homomorphism.  The second, \af{interp-prod}, shows how to express the interpretation of a term in a product algebra.
\ifshort
We omit the formal definitions and proofs of these types, but see the \ualmodule{Types.Func.Properties} module of the \agdaalgebras library for details.
\else

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Environment 𝑨 using ( ⟦_⟧ )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )
 open Setoid 𝔻[ 𝑩 ] using ( _≈_ ; refl )
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a       = refl
 comm-hom-term (node f t) a  =
  begin
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
\fi

%% -------------------------------------------------------------------------------------

\section{Equational Logic}
\label{equational-logic}

\paragraph*{Basic definitions}
%\label{model-theory-basic-definitions}

%\subsubsection*{Term identities and the ⊧ relation}
Given a  signature \ab{𝑆} and a context of variable symbols \ab X, a \defn{term equation} or \defn{identity}
(in this signature and context) is an ordered pair (\ab p , \ab q) of 𝑆-terms.
(Informally, such an equation is often denoted by \ab p \af{≈} \ab q.)

For instance, if the context is the type \ab X : \ap{Type} \ab{χ}, then a term equation
is a pair inhabiting the Cartesian product type \ad{Term}~\ab{X} \aof{×} \ad{Term}~\ab{X}.

If \ab{𝑨} is an \ab{𝑆}-algebra we say that \ab{𝑨} \emph{satisfies} \ab p \af{≈} \ab q if
for all environments \ab{ρ} : \ab X \as{→} \aof{𝔻[~\ab{𝑨}~]} (assigning values in the domain of
\ab{𝑨} to variable symbols in \ab X) we have \aof{⟦~\ab{p}~⟧} \aofld{⟨\$⟩} \ab{ρ} \af{≈}
\aof{⟦~\ab{q}~⟧} \aofld{⟨\$⟩} \ab{ρ}.  In other words, when they are interpreted in the algebra \ab{𝑨},
the terms \ab{p} and \ab{q} are equal (no matter what values in \ab{𝑨} are assigned to variable symbols in \ab{X}).
In this situation, we write
%\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}⊧\AgdaUnderscore{}≈\AgdaUnderscore{}}}\AgdaSpace{}%
\ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q} and say that \ab{𝑨} \defn{models} the identity \ab{p}~\af{≈}~\ab{q}.
If \ab{𝒦} is a class of algebras, all of the same signature, we write \ab{𝒦}~\aof{⊫}~\ab{p}~\aof{≈}~\ab{q}
and say that \ab{𝒦} \defn{models} the identity \ab{p}~\af{≈}~\ab{q} provided for every \ab{𝑨} \aof{∈} \ab{𝒦},
we have \ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q}.

\begin{code}

_⊧_≈_ : Algebra α ρᵃ → Term Γ → Term Γ → Type _
𝑨 ⊧ p ≈ q = Equal p q where open Environment 𝑨

_⊫_≈_ : Pred (Algebra α ρᵃ) ℓ → Term Γ → Term Γ → Type _
𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}
%% \AgdaFunction{Pred}\AgdaSymbol{(}\AgdaDatatype{Term}\AgdaSpace{}%
%% \AgdaBound{X}\AgdaSpace{}%
%% \AgdaOperator{\AgdaFunction{×}}\AgdaSpace{}%
%% \AgdaDatatype{Term}\AgdaSpace{}%
%% \AgdaBound{X}\AgdaSymbol{)}\AgdaSpace{}%
%% \AgdaSymbol{\AgdaUnderscore{}}\<%
We represent a collection of identities as a predicate over pairs of terms---for example,
\ab{ℰ}~:~\af{Pred}(\ad{Term}~\ab{X}~\aof{×}~\ad{Term}~\ab{X})~\au---and we denote by
\ab{𝑨}~\aof{⊨}~\ab{ℰ} the assertion that the algebra \ab{𝑨} models every equation
\ab{p}~\afld{≈}~\ab{q} % (i.e., every \AgdaPair{p}{q}) in \ab{ℰ}.

\begin{code}

_⊨_ : (𝑨 : Algebra α ρᵃ) → Pred(Term Γ × Term Γ) (ov χ) → Type _
𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

\end{code}

%\subsubsection*{Equational theories and classes}
In (informal) equational logic, if \ab{𝒦} is a class of structures and \ab{ℰ} a set of term identities, then
the set of term equations modeled by \ab{𝒦} is denoted \af{Th}~\ab{𝒦} and called the \defn{equational theory} of \ab{𝒦},
while the class of structures modeling \ab{ℰ} is denoted by \af{Mod}~\ab{ℰ} and is called the \defn{equational class axiomatized} by \ab{ℰ}.
These notions may be formalize in type theory as follows.

\begin{code}

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

\end{code}

%\subsubsection*{The entailment relation}
We represent entailment in type theory by defining an inductive type that is similar to the one Andreas Abel defined for formalizing Birkhoff's completeness theorem (\textit{op.~cit.}).

\begin{code}

data _⊢_▹_≈_  (ℰ : {Y : Type χ} → Pred(Term Y × Term Y) (ov χ)) :
              (X : Type χ)(p q : Term X) → Type (ov χ) where

 hyp         :  ∀{Y}{p q : Term Y} → (p , q) ∈ ℰ → ℰ ⊢ _ ▹ p ≈ q
 app         :  ∀{Y}{ps qs : ∥ 𝑆 ∥ 𝑓 → Term Y}
                          → (∀ i → ℰ ⊢ Y ▹ ps i ≈ qs i) → ℰ ⊢ Y ▹ (node 𝑓 ps) ≈ (node 𝑓 qs)
 sub         :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → (σ : Sub Δ Γ) → ℰ ⊢ Δ ▹ (p [ σ ]) ≈ (q [ σ ])
 reflexive   :  ∀{p}      → ℰ ⊢ Γ ▹ p ≈ p
 symmetric   :  ∀{p q}    → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ p
 transitive  :  ∀{p q r}  → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r → ℰ ⊢ Γ ▹ p ≈ r

\end{code}

Entailment is \defn{sound} in the following sense: % for every algebra \ab{𝑨} that models the equations in \ab{ℰ},
if \ab{ℰ} entails \ab p \aof{≈} \ab q and \ab{𝑨} \aof{⊨} \ab{ℰ}, then \ab p \aof{≈} \ab q holds in \ab{𝑨}.  In other terms,
the derivation \ab{ℰ} \aod{⊢} \ab X \aod{▹} \ab p \aod{≈} \ab q implies that \ab p \aof{≈} \ab q holds in every model of \ab{ℰ}.
We will apply this result---called \af{sound} and borrowed from Andreas Abel's proof of Birkhoff's completeness theorem (\textit{op.~cit.})---only once below %(in §\ref{basic-properties-of-free-algebras})%
\ifshort
, so we omit its straightforward formalization.
\else
; nonetheless, here is the formalization due to Abel.

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
   ⟦ p  [ σ ]  ⟧ ⟨$⟩         ρ  ≈⟨   substitution p σ ρ    ⟩
   ⟦ p         ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ  ≈⟨   sound Epq (⟦ σ ⟧s ρ)  ⟩
   ⟦ q         ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ  ≈˘⟨  substitution q σ ρ    ⟩
   ⟦ q  [ σ ]  ⟧ ⟨$⟩         ρ  ∎
 sound (reflexive   {p = p}                 ) = reflᵉ   EqualIsEquiv {x = p}
 sound (symmetric   {p = p}{q}     Epq      ) = symᵉ    EqualIsEquiv {x = p}{q}     (sound Epq)
 sound (transitive  {p = p}{q}{r}  Epq Eqr  ) = transᵉ  EqualIsEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
\end{code}
\fi


\paragraph*{The Closure Operators H, S, P and V}
%\label{the-closure-operators-h-s-p-and-v}
Fix a signature \ab{𝑆}, let \ab{𝒦} be a class of \ab{𝑆}-algebras, and define
\begin{itemize}
\item \af H \ab{𝒦} = algebras isomorphic to homomorphic images of members of \ab{𝒦};
\item \af S \ab{𝒦} = algebras isomorphic to subalgebras of a members of \ab{𝒦};
\item \af P \ab{𝒦} = algebras isomorphic to products of members of \ab{𝒦}.
\end{itemize}
A straight-forward verification confirms that \af H, \af S, and \af P are \emph{closure operators} (expansive, monotone, and idempotent).  A class \ab{𝒦} of \ab{𝑆}-algebras is said to be \emph{closed under the taking of homomorphic images} provided \af H \ab{𝒦} \aof{⊆} \ab{𝒦}. Similarly, \ab{𝒦} is \emph{closed under the taking of subalgebras} (resp., \emph{arbitrary products}) provided \af S \ab{𝒦} \aof{⊆} \ab{𝒦} (resp., \af P \ab{𝒦} \aof{⊆} \ab{𝒦}). The operators \af H, \af S, and \af P can be composed with one another repeatedly, forming yet more closure operators.

% An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class \af H \ab{𝒦} (resp., \af S \ab{𝒦}; resp., \af P \ab{𝒦}) is closed under isomorphism.

A \emph{variety} is a class of \ab{𝑆}-algebras that is closed under the taking of
homomorphic images, subalgebras, and arbitrary products.  To represent varieties
we define types for the closure operators \af H, \af S, and \af P that are composable.
Separately, we define a type \af V which represents closure under all three
operators, \af H, \af S, and \af P.  Thus, if \ab{𝒦} is a class of \ab{𝑆}-algebras, then
\af V \ab{𝒦} := \af H (\af S (\af P \ab{𝒦})), and \ab{𝒦} is a variety iff \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.

We now define the type \af H to represent classes of algebras that include all homomorphic images of algebras in the class---i.e., classes that are closed under the taking of homomorphic images---the type \af S to represent classes of algebras that closed under the taking of subalgebras, and the type \af P to represent classes of algebras closed under the taking of arbitrary products.

\begin{code}

module _ {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ

 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) _
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

\end{code}

As mentioned, \af S is a closure operator.  The facts that \af S is monotone and expansive won't be needed, so we omit their proofs.
However, we do make use of idempotence of \af S, so let us pause to prove that property here.

\begin{code}

S-idem :  {𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}
 →        S{β = γ}{ρᶜ} (α ⊔ ρᵃ  ⊔ ℓ) (S{β = β}{ρᵇ} ℓ 𝒦) ⊆ S{β = γ}{ρᶜ} ℓ 𝒦

S-idem (𝑨 , (𝑩 , sB , A≤B) , x≤A) = 𝑩 , (sB , ≤-transitive x≤A A≤B)

\end{code}
Finally, we define the \defn{varietal closure} of a class \ab{𝒦} to be the class \af{V} \ab{𝒦} := \af{H} (\af{S} (\af{P} \ab{𝒦})).
(Recall, \ab{𝒦} is called a \defn{variety} if \af{V} \ab{𝒦} = \ab{𝒦}.)
\begin{code}

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

\end{code}

The binary relation \aof{⊧} would be practically useless if it were not an \emph{algebraic invariant} (i.e., invariant under isomorphism). Let us now verify that the models relation we defined above has this essential property.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where

 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ =
  begin
   ⟦ p ⟧     ⟨$⟩            ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
   ⟦ p ⟧     ⟨$⟩ (f  ∘ (g ∘ ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
   f(⟦ p ⟧ᴬ  ⟨$⟩       (g ∘ ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
   f(⟦ q ⟧ᴬ  ⟨$⟩       (g ∘ ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
   ⟦ q ⟧     ⟨$⟩ (f  ∘ (g ∘ ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
   ⟦ q ⟧     ⟨$⟩            ρ    ∎
  where
  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
  open Environment 𝑨     using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩     using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑩 ]

\end{code}
Identities modeled by an algebra \ab{𝑨} are also modeled by every subalgebra of \ab{𝑨}.
\ifshort
We will refer to this fact as \af{⊧-S-invar}. We omit its proof since it is similar to the proof of
\af{⊧-I-invar}.
\else
This fact is formalized in Agda as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where

 ⊧-S-invar : 𝑨 ⊧ p ≈ q →  𝑩 ≤ 𝑨  →  𝑩 ⊧ p ≈ q
 ⊧-S-invar Apq B≤A b = ∥ B≤A ∥ (ξ b)
  where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  private hh = ∣ B≤A ∣ ; h = _⟨$⟩_ ∣ hh ∣

  ξ : ∀ b → h (⟦ p ⟧ ⟨$⟩ b) ≈ h (⟦ q ⟧ ⟨$⟩ b)
  ξ b = begin
         h (⟦ p ⟧  ⟨$⟩         b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ    ⟨$⟩  (h  ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ    ⟨$⟩  (h  ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
         h (⟦ q ⟧  ⟨$⟩         b)  ∎ where open SetoidReasoning 𝔻[ 𝑨 ]

\end{code}
\fi
Next, an identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.
\ifshort
We omit the formal proof of this fact, and refer to it as \af{⊧-P-invar} below.
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

%\paragraph*{Identity preservation}
The classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦}, and \af V \ab{𝒦} all satisfy the same set of equations.  We will only use a subset of the inclusions used to prove this fact. For complete proofs, see the
\ualmodule{Varieties.Func.Preservation} module of the \agdaalgebras library.
\ifshort
Specifically, we will cite the following facts, whose formal proofs we omit.
\else
First we prove that the closure operator \af H is compatible with identities that hold in the given class.

\begin{code}

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
\end{code}
\fi

\begin{code}

 H-id1 : 𝒦 ⊫ p ≈ q → (H {β = α}{ρᵃ}ℓ 𝒦) ⊫ p ≈ q
\end{code}\ifshort\else
\begin{code}
 H-id1 σ 𝑩 (𝑨 , kA , BimgOfA) ρ =
  begin
   ⟦ p ⟧      ⟨$⟩             ρ   ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)⟩
   ⟦ p ⟧      ⟨$⟩ (φ ∘ φ⁻¹  ∘ ρ)  ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)      ⟩
   φ (⟦ p ⟧ᴬ  ⟨$⟩ (    φ⁻¹  ∘ ρ)) ≈⟨   cong ∣ φh ∣ (IH (φ⁻¹ ∘ ρ))        ⟩
   φ (⟦ q ⟧ᴬ  ⟨$⟩ (    φ⁻¹  ∘ ρ)) ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)      ⟩
   ⟦ q ⟧      ⟨$⟩ (φ ∘ φ⁻¹  ∘ ρ)  ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)⟩
   ⟦ q ⟧      ⟨$⟩             ρ   ∎
    where
    IH : 𝑨 ⊧ p ≈ q
    IH = σ 𝑨 kA
    φh : hom 𝑨 𝑩
    φh = ∣ BimgOfA ∣
    φE : IsSurjective ∣ φh ∣
    φE = ∥ BimgOfA ∥
    φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    φ⁻¹ = SurjInv ∣ φh ∣ φE
    private φ = (_⟨$⟩_ ∣ φh ∣)
    open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
    open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

\end{code}

Similarly for \af S and the obvious converse, though barely worth mentioning, must be formally proved as well since we use it below.
\fi
\begin{code}
 S-id1 : 𝒦 ⊫ p ≈ q → (S {β = α}{ρᵃ} ℓ 𝒦) ⊫ p ≈ q
\end{code}\ifshort\else
\begin{code}
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

\end{code}
\fi
\begin{code}
 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
\end{code}\ifshort\else
\begin{code}
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

\end{code}
Finally, we have analogous pairs of implications for \af P and \af V.  In each case, we will only need the first implication, so we omit the formal proof of the others.

\fi

\begin{code}
 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P {β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
\end{code}\ifshort\else
\begin{code}
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  ih : ∀ i → 𝒜 i ⊧ p ≈ q
  ih i = σ (𝒜 i) (kA i)
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} ih

module _ {X : Type χ}{ι : Level}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

\end{code}
\fi
\begin{code}
 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
\end{code}\ifshort\else
\begin{code}
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
The term algebra \af{𝑻} \ab X is \emph{absolutely free} (or \emph{universal}, or
\emph{initial}) for algebras in the signature \ab{𝑆}. That is, for every
\ab{𝑆}-algebra \ab{𝑨}, the following hold.

\begin{itemize}
\item Every function from \ab{X} to \af{𝕌[ \ab{𝑨} ]} lifts to a homomorphism from \af{𝑻} \ab{X} to \ab{𝑨}.
\item The homomorphism that exists by the previous item is unique.
\end{itemize}

We now prove the first of these facts in \agda.\footnote{For the proof of uniqueness, see the \ualmodule{Terms.Func.Properties} module of the \agdaalgebras library.}
%, starting with the fact that every map from \ab{X} to
%\af{𝕌[ \ab{𝑨} ]} lifts to a map from \af{𝕌[ \T{X} ]} (= \af{Term} \ab{X}) to
%\af{𝕌[ \ab{𝑨} ]} in a natural way, by induction on the structure of the given term.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , (λ i → flcong (x i)))

\end{code}
Naturally, at the base step of the induction, when the term has the form \aic{ℊ}
\ab x, the free lift of \ab h agrees with \ab h.  For the inductive step, when the
given term has the form \aic{node} \ab f \ab t, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm \ab t \ab i under the free lift of \ab h, define the free lift at the
full term by applying \ab f \aof{̂} \ab{𝑨} to the images of the subterms.
The free lift so defined is a homomorphism by construction. Indeed, here is the trivial proof.

\begin{code}

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func , hhom
  where
  hfunc : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
  hfunc = free-lift-func

  hcomp : compatible-map (𝑻 X) 𝑨 free-lift-func
  hcomp {f}{a} = cong (Interp 𝑨) (≡.refl , (λ i → (cong free-lift-func){a i} ≃-isRefl))

  hhom : IsHom (𝑻 X) 𝑨 hfunc
  hhom = mkhom (λ{f}{a} → hcomp{f}{a})

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ} where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}

\paragraph*{The relatively free algebra}
We now define the algebra \AgdaOperator{\AgdaFunction{𝔽[}}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]}},
which represents the \defn{relatively free algebra} over \ab X.
The domain of the free algebra is a setoid whose \afld{Carrier} is the type \ad{Term} \ab X of {𝑆}-terms
in \ab X. The interpretation of an operation in the free algebra is simply the operation itself.
%This works since \ab{ℰ} \aod{⊢} \ab X \aod{▹\au{}≈\{}} is a congruence.

\begin{code}

module FreeAlgebra {χ : Level}(ℰ : {Y : Type χ} → Pred (Term Y × Term Y) (ov χ)) where

 FreeDomain : Type χ → Setoid _ _
 FreeDomain X =
  record  { Carrier        = Term X
          ; _≈_            = ℰ ⊢ X ▹_≈_
          ; isEquivalence  = record { refl = reflexive ; sym = symmetric ; trans = transitive } }

 𝔽[_] : Type χ → Algebra (ov χ) _
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp
  where
  FreeInterp : ∀ {X} → ⟨ 𝑆 ⟩ (FreeDomain X) ⟶ FreeDomain X
  FreeInterp ⟨$⟩ (f , ts)       = node f ts
  cong FreeInterp (≡.refl , h)  = app h
\end{code}

\paragraph*{The natural epimorphism} % from 𝑻 X to 𝔽[ X ]}
We now define the natural epimorphism from \T{X} onto the relatively free algebra \Free{X} and prove that
the kernel of this morphism is the congruence of \T{X} defined by the identities modeled by (\af S \ab{𝒦}, hence by) \ab{𝒦}.

\begin{code}

module FreeHom {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 open FreeAlgebra {χ = c} (Th 𝒦) using ( 𝔽[_] )

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

\end{code}

As promised, we prove that the kernel of the natural epimorphism is the congruence defined by the identities modelled by \ab{𝒦}.

\begin{code}

 kernel-in-theory : {X : Type c} → ker ∣ homF[ X ] ∣ ⊆ Th (V ℓ ι 𝒦)
 kernel-in-theory {X = X} {p , q} pKq 𝑨 vkA = V-id1{ℓ = ℓ}{p = p}{q} (ζ pKq) 𝑨 vkA
  where
  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨
\end{code}

\paragraph*{The universal property}

\begin{code}

module _  {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeHom {ℓ = ℓ} {𝒦}
 open FreeAlgebra {χ = c}(Th 𝒦)  using ( 𝔽[_] )
 open Setoid 𝔻[ 𝑨 ]              using ( refl ; sym ; trans ) renaming  ( Carrier  to A )

 F-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] 𝑨
 F-ModTh-epi A∈ModThK = φ , isEpi
  where
  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  = trans  ( sym (free-lift-interp{𝑨 = 𝑨} id p) )
                     ( trans  ( A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                               ( free-lift-interp{𝑨 = 𝑨} id q ) )
  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  compatible (isHom isEpi) = cong (Interp 𝑨) (≡.refl , (λ _ → refl))
  isSurjective isEpi {y} = eq (ℊ y) refl

 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
\end{code}



%% -------------------------------------------------------------------------------------

\section{Birkhoff's Variety Theorem}

\subsection{Informal statement and proof}
Let \ab{𝒦} be a class of algebras. Recall that \ab{𝒦} is a \emph{variety} provided it is closed under homomorphisms, subalgebras and products; equivalently, \af{H} (\af{S} (\af{P} \ab{𝒦})) ⊆ \ab{𝒦}.
(As \af{H}, \af{S}, and \af{P} are closure operators, the inclusion \ab{𝒦} ⊆ \af{H} (\af{S} (\af{P} \ab{𝒦}))
is always valid, for every class \ab{𝒦}.)
We call \ab{𝒦} an \emph{equational class} if it is precisely the class of all models of some set of term identities.

It is easy to prove that \emph{every equational class is a variety}.  Indeed, suppose \ab{𝒦} is an equational
class and suppose the set \ab{ℰ} of term identities \defn{axiomatizes} \ab{𝒦}. That is, \ab{𝒦} \af{⊫} \ab{ℰ} and for all \ab{𝑨} we have \ab{𝑨} \af{⊨} \ab{ℰ} \as{→} \ab{𝑨} \af{∈} \ab{𝒦}. Then, since the classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦} and \ab{𝒦} all satisfy the same set of equations, we have \af{H} (\af{S} (\af{P} \ab{𝒦})) ⊫ \ab{ℰ}, so \af{V} \ab{𝒦} = \af{H} (\af{S} (\af{P} \ab{𝒦})) ⊆ \ab{𝒦}; that is, \ab{𝒦} is a variety. The converse assertion---that \emph{every variety is an equational class}---is more difficult to prove and is known as Birkhoff's variety theorem.

We now describe the standard informal proof of Birkhoff's theorem and then present a formal, constructive, type-theoretic proof of this theorem in Agda.

Let \ab{𝒦} be an arbitrary variety.  We will describe a set of equations that axiomatizes \ab{𝒦}, thus showing that \ab{𝒦} is an equational class.  A natural choice is the set \af{Th} \ab{𝒦} of all equations that hold in \ab{𝒦}. We will prove that \ab{𝒦} is precisely the class of structures
modeling \af{Th} \ab{𝒦}
.
Define \ab{𝒦⁺} = \af{Mod} (\af{Th} \ab{𝒦}).  Clearly, \ab{𝒦} \aof{⊆} \ab{𝒦⁺}. We prove the reverse inclusion. Let \ab{𝑨} \af{∈} \ab{𝒦⁺}.
To complete the proof it suffices to find an algebra \ab{𝑭} belonging to \af{S} (\af{P} \ab{𝒦}) such that
\ab{𝑨} is the homomorphic image of \ab{𝑭}. Indeed, this will prove that \ab{𝑨} belongs to
\af{H} (\af{S} (\af{P} \ab{𝒦})), which is \ab{𝒦}, since we assumed that \ab{𝒦} is a variety.

Let \ab{X} be a set of cardinality max(|A|, ω), and let \ab{ρ} : \ab{X} \as{→} \af{𝕌[ \ab{𝑨} ]} be a surjective valuation of variable symbols in the domain of \ab{𝑨}. By the \af{lift-hom} lemma that we formalized above, the map \ab{ρ} extends to an epimorphism \ab{ρ⁺} from \T{X} onto \ab{𝕌[ \ab{𝑨} ]}.
Furthermore, since \ab{𝔽} := \T{X}/Θ, there is an epimorphism \ab{g} : \T{X} \as{→} \ab{𝔽}.
We claim that \af{ker} \ab g \af{⊆} \af{ker} \ab h. If the claim is true, then there is a map \ab{f} : \ab{𝔽} \as{→} \ab{𝑨} such that \ab f \af{∘} \ab g = \ab h.
Since \ab h is epic, so is \ab f. Hence \ab{𝑨} \af{∈} \af{𝖧} (\af{𝔽} \ab X) \aof{⊆} \ab{𝒦⁺} completing the proof.


\subsection{Formal statement and proof}

We now show how to formally express and prove the twin assertions that
(i) every equational class is a variety and (ii) every variety is an equational class.

\paragraph*{Every equational class is a variety}
For (i), we need an arbitrary equational class. To obtain one, we start with an arbitrary
collection \ab{ℰ} of equations and let \ab{𝒦} = \af{Mod} \ab{ℰ}, the equational class determined by \ab{ℰ}.
We prove that \ab{𝒦} is a variety by showing that \ab{𝒦} = \af{V} \ab{𝒦}.
The inclusion \ab{𝒦} \aof{⊆} \af V \ab{𝒦}, which holds for all classes \ab{𝒦}, is called the \defn{expansive} property of \af{V}.
The converse inclusion \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, on the other hand, requires the hypothesis that \ab{𝒦} is an equation class.
We now formalize each of these inclusions.


\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 V-expa : 𝒦 ⊆ V ℓ ι 𝒦
 V-expa {x = 𝑨} kA = 𝑨 , (𝑨 , (⊤ , (λ _ → 𝑨) , (λ _ → kA) , Goal) , ≤-reflexive) , IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ] using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ] using () renaming ( refl to refl⨅ )

  to⨅ : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  (to⨅ ⟨$⟩ x) = λ _ → x
  cong to⨅ xy = λ _ → xy

  from⨅ : 𝔻[ ⨅ (λ _ → 𝑨) ] ⟶ 𝔻[ 𝑨 ]
  (from⨅ ⟨$⟩ x) = x tt
  cong from⨅ xy = xy tt

  Goal : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal = mkiso (to⨅ , mkhom refl⨅) (from⨅ , mkhom refl) (λ _ _ → refl) (λ _ → refl)

\end{code}
Earlier we proved the following identity preservation lemma:
\af{V-id1} : \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q \as{→} \af{V} \ab{ℓ} \ab{ι} \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q.
Thus, if \ab{𝒦} is an equational class, then \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.  The
\af{Birkhoff|eqcl→var} lemma below formalizes this fact.

\begin{code}

module _ {ℓ : Level}{X : Type ℓ}{ℰ : {Y : Type ℓ} → Pred (Term Y × Term Y) (ov ℓ)} where
 private ι = ov ℓ

 private 𝒦 = Mod{α = ℓ}{ℓ}{X} ℰ     -- an arbitrary equational class

 EqCl⇒Var : V ℓ ι 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨}vA{p}{q} pℰq ρ = V-id1{ℓ = ℓ}{𝒦 = 𝒦}{p}{q}(λ _ x τ → x pℰq τ) 𝑨 vA ρ

\end{code}
Together, \af{V-expa} and \af{Eqcl⇒Var} prove that every equational class is a variety.


\paragraph*{Every variety is an equational class}
To prove statement (ii), we need an arbitrary variety; to obtain one, we start with an arbitrary class
\ab{𝒦} of \ab{𝑆}-algebras and take its \emph{varietal closure}, \af{V} \ab{𝒦}.
We prove that \af{V} \ab{𝒦} is an equational class by showing it is precisely the collection of
algebras that model the equations in \af{Th} (\af{V} \ab{𝒦}); that is, we prove
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})).
The inclusion \af{V} \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a simple consequence of the fact that \af{Mod} \af{Th} is a closure operator. Nonetheless, completeness demands
that we formalize this fact, however trivial is its proof.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p} {q} x ρ = x 𝑨 vA ρ

\end{code}

It remains to prove the converse inclusion, \af{Mod} (\af{Th} (V 𝒦)) \aof{⊆} \af{V} \ab{𝒦},
which is the main focus of the rest of the paper.  We proceed as follows:

\begin{enumerate}
\item Construct an algebra \ab{𝑪} that is a product of algebras in \af{S} \ab{𝒦}, hence belongs to \af{P} \af{S} \ab{𝒦} ⊆ \af{S} \af{P} \ab{𝒦}.
\item Prove that \aof{𝔽[ \ab{X} ]} is a subalgebra of \ab{𝑪}, which puts \aof{𝔽[ \ab{X} ]} in \af{S} (\af{S} (\af{P} \ab{𝒦})) (= \af{S} (\af{P} \ab{𝒦})).
\item Prove that every algebra in \af{Mod} (\af{Th} (V 𝒦)) is a homomorphic image of
\aof{𝔽[ \ab{X} ]} and thus belongs to \af{H} (\af{S} (\af{P} \ab{𝒦})) (= \af{V} \ab{𝒦}).
\end{enumerate}

We will define the algebra \ab{𝑪} to be the product of \emph{all} algebras in \af{S} \ab{𝒦}, and this requires that we index the algebras in \af{S} \ab{𝒦}.
In fact, we will need to associate each ``indexing pair'' (\ab{𝑨} , \ab p) (where \ab p : \ab{𝑨} \af{∈} \af{S} \ab{𝒦}) with an arbitrary environment
\ab{ρ} : \ab X \as{→} \aof{𝕌[ \ab{𝑨} ]}. Consequently, the indices of the product will be triples (\ab{𝑨} , \ab p, \ab{ρ}) ranging over all algebras in \af{S} \ab{𝒦} and all
environments assigning values in the domain of \ab{𝑨} to variables in \ab X.  Here is the construction of \ab{𝑪}.

\begin{code}

 open FreeHom {ℓ = ℓ} {𝒦}
 open FreeAlgebra {χ = c}(Th 𝒦)  using ( 𝔽[_] )
 open Environment                using ( Env )

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → Algebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 𝑪 : Algebra ι ι
 𝑪 = ⨅ 𝔄⁺

 skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where open Setoid 𝔻[ 𝔄⁺ i ] using ( _≈_ ) ; open Environment (𝔄⁺ i) using ( ⟦_⟧ )

\end{code}
The type \af{skEqual} provides a term identity \ab p \af{≈} \ab q for each index \ab i = (\ab{𝑨} , \ab{p} , \ab{ρ}) of the product.
%(here, as above, \ab{𝑨} is an algebra, \ab{sA} is a proof that \ab{𝑨} belongs to \af{S} \ab{𝒦}, and \ab{ρ} is an environment).
%map assigning values in the domain of \ab{𝑨} to variable symbols in \ab X).
\ifshort\else
Later we prove that if the identity \ab{p} \af{≈} \ab q holds in all \ab{𝑨} \aof{∈} \af S \ab{𝒦} (for all environments), then \ab p \af{≈} \ab q
holds in the relatively free algebra \Free{X}; equivalently, the pair (\ab p , \ab q) belongs to the
kernel of the natural homomorphism from \T{X} onto \Free{X}. We will use that fact to prove
that the kernel of the natural hom from \T{X} to \ab{𝑪} is contained in the kernel of the natural hom from \T{X} onto \Free{X},
whence we construct a monomorphism from \Free{X} into \ab{𝑪}, and thus \Free{X} is a subalgebra of \ab{𝑪},
so belongs to \af S (\af P \ab{𝒦}).
\fi

\begin{code}

 homC : hom (𝑻 X) 𝑪
 homC = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)
\end{code}
\ifshort\else
\begin{code}

 kerF⊆kerC : ker ∣ homF[ X ] ∣ ⊆ ker ∣ homC ∣
 kerF⊆kerC {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; sym ; trans )
  open Environment 𝑨  using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t

  ζ : ∀{p q} → (Th 𝒦) ⊢ X ▹ p ≈ q → 𝒦 ⊫ p ≈ q
  ζ x 𝑨 kA = sound (λ y ρ → y 𝑨 kA ρ) x where open Soundness (Th 𝒦) 𝑨

  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = S-id1{ℓ = ℓ}{p = p}{q} (ζ pKq) 𝑨 sA ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))
\end{code}
\fi
\begin{code}

 homFC : hom 𝔽[ X ] 𝑪
 homFC = ∣ HomFactor 𝑪 homC homF[ X ] kerF⊆kerC (isSurjective ∥ epiF[ X ] ∥) ∣

\end{code}
If \AgdaPair{p}{q} belongs to the kernel of \af{hom𝑪}, then
\af{Th} \ab{𝒦} includes the identity \ab{p} \af{≈} \ab{q}---that is,
\af{Th} \ab{𝒦} \af{⊢} \ab X \af{▹} \ab{p} \af{≈} \ab{q}. Equivalently,
if the kernel of \af{hom𝑪} is contained in that of \af{hom𝔽[ X ]}.
\ifshort
We omit the formal proof of this lemma and merely display its formal statement, which is the following.
\else
We formalize this fact as follows.

\begin{code}

 kerC⊆kerF : ∀{p q} → (p , q) ∈ ker ∣ homC ∣ → (p , q) ∈ ker ∣ homF[ X ] ∣
\end{code}
\ifshortelse
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
   open Environment (𝔄⁺ i)  using ( ⟦_⟧ )
   open Setoid 𝔻[ 𝔄⁺ i ]    using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
   goal  = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
         ( trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))

\end{code}
\fi
We conclude that the homomorphism from \Free{X} to \af{𝑪} is injective, whence it follows that \Free{X} is (isomorphic to) a subalgebra of \af{𝑪}.

\begin{code}

 monFC : mon 𝔽[ X ] 𝑪
 monFC = ∣ homFC ∣ , isMon
  where
  isMon : IsMon 𝔽[ X ] 𝑪 ∣ homFC ∣
  isHom isMon = ∥ homFC ∥
  isInjective isMon {p}{q} φpq = kerC⊆kerF φpq

 F≤C : 𝔽[ X ] ≤ 𝑪
 F≤C = mon→≤ monFC

\end{code}
Using the last result we prove that \Free{X} belongs to \af{S} (\af{P} \ab{𝒦}). This requires one more technical lemma concerning the classes \af{S} and \af{P};
specifically,
\ifshort
\af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}) holds for every class \ab{𝒦}.
The \ualmodule{Varieties.Func.Preservation.lagda} module contains the formal statement and proof of that result (called \af{PS⊆SP}) which we omit.
\else
a product of subalgebras of algebras in a class is a subalgebra of a product of algebras in the class;
in other terms, \af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}), for every class \ab{𝒦}.
We state and prove this in Agda as follows.

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

%We conclude this subsection with the proof that \Free{X} belongs to \af{S} (\af{P} \ab{𝒦}).

\begin{code}

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = S-idem (𝑪 , (spC , F≤C))
  where
  psC : 𝑪 ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  psC = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))
  spC : 𝑪 ∈ S ι (P ℓ ι 𝒦)
  spC = PS⊆SP psC

\end{code}
Finally, we prove that every algebra in \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a homomorphic image of \af{𝔽[ \ab{X} ]}, for some \ab{X}.

\begin{code}

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra {χ = c}(Th 𝒦) using ( 𝔽[_] )

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
  AimgF = ∘-hom ∣ φ ∣ (from Lift-≅) ,
          ∘-IsSurjective _ _ ∥ φ ∥ (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

\end{code}

It follows immediately from \af{ModTh-closure} and \af{Var⇒EqCl} that
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) holds for every class \ab{𝒦} of \ab{𝑆}-algebras.
Thus, every variety is an equational class. This completes the formal proof of Birkhoff's variety theorem.


%% \paragraph*{Th 𝒦 ⊆ Th (V 𝒦)}
%% From \af{V-id1} it follows that if \ab{𝒦} is a class of algebras, then the set of identities
%% modeled by the algebras in \ab{𝒦} is contained in the set of identities modeled by the algebras
%% in \af V \ab{𝒦}.  In other terms, \af{Th} \ab{𝒦} \aof{⊆} \af{Th} (\af V \ab{𝒦}).  We formalize
%% this observation as follows.
%% begin{code}[hide]
%% classIds-⊆-VIds : 𝒦 ⊫ p ≈ q  → (p , q) ∈ Th (V ℓ ι 𝒦)
%% classIds-⊆-VIds pKq 𝑨 = V-id1 pKq 𝑨
%% end{code}


