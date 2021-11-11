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

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )

module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where

open import  Agda.Primitive               using     ( _⊔_ ; lsuc )
                                          renaming  ( Set to Type )
open import  Data.Product                 using     ( _×_  ; Σ-syntax ; _,_ ; Σ )
                                          renaming  ( proj₁ to  fst ; proj₂ to snd )
open import  Function                     using     ( id ; Surjection ; flip ; Injection ; _∘_ )
                                          renaming  ( Func to _⟶_ )
open import  Level                        using     ( Level )
open import  Relation.Binary              using     ( Setoid ; IsEquivalence ; Rel )
open import  Relation.Binary.Definitions  using     ( Sym ; Symmetric ; Trans ; Transitive ; Reflexive )
open import  Relation.Binary.PropositionalEquality
                                          using     ( _≡_ )
open import  Relation.Unary               using     ( Pred ; _⊆_ ; _∈_ )

import  Function.Definitions                   as FD
import  Relation.Binary.PropositionalEquality  as ≡
import  Relation.Binary.Reasoning.Setoid       as SetoidReasoning

open _⟶_     using ( cong ) renaming ( f to _⟨$⟩_ )

\end{code}
\ifshort\else
\begin{code}
open Setoid  using ( Carrier ; isEquivalence )
private variable
 α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level
 Γ Δ : Type χ
 𝑓 : fst 𝑆
\end{code}
\fi
Note, in particular, we prefer to use \AgdaPrimitive{Type} to denote the
built-in \AgdaPrimitive{Set} type, and the infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, to denote the \AgdaRecord{Func}
type of the standard library.  We use \AgdaField{fst} and \AgdaField{snd} in
place of \AgdaField{proj₁} and  \AgdaField{proj₂} for the first and second
projections out of the product type,
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}, and,
when it improves readability of the code, we use the alternative notation
\AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}} (resp.) for these projections.
\ifshort
\else
\begin{code}
module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}
\fi

%% -----------------------------------------------------------------------------
\subsection{Setoids}
A \emph{setoid} is a type packaged with an equivalence relation on the collection
of inhabitants of that type.  Setoids are useful for representing classical
(set-theory-based) mathematics in a constructive, type-theoretic way because
most mathematical structures are assumed to come equipped with some (often
implicit) equivalence relation manifesting a notion of equality of elements,
and therefore a type-theoretic representation of such a structure should
also model its equality relation.

The \agdaalgebras library was first developed without the use of setoids,
opting instead for specially constructed experimental quotient types.
However, this approach resulted in code that was hard to comprehend and
it became difficult to determine whether the resulting proofs were fully
constructive.  In particular, our initial proof of the Birkhoff variety theorem
required postulating function extensionality, an axiom that is not provable in
pure Martin-Löf type theory (MLTT). [reference needed]

In contrast, our current approach using setoids makes the equality relation
of a given type explicit and this transparency can make it easier to determine the
correctness and constructivity of the proofs. Using setiods we need
no additional axioms beyond MLTT; in particular, no function
extensionality axioms are postulated in our current formalization of Birkhoff's
variety theorem.

%% -----------------------------------------------------------------------------
\subsection{Setoid functions}
In addition to the \ar{Setoid} type, much of our code employs the
standard library's \ar{Func} type which represents a function from one
setoid to another and packages such a function with a proof (called \afld{cong}) that
the function respects the underlying setoid equalities. As mentioned above, we renamed
\ar{Func} to the more visually appealing infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, and  throughout the paper we
refer to inhabitants of this type as ``setoid functions.''

\ifshort\else
An example of a setoid function is the identity function from a setoid to itself.
We define it, along with a binary composition operation for setoid functions, \AgdaOperator{\AgdaFunction{⟨∘⟩}}, as follows.

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
We define a data type that represents the semantic concept of the \emph{image} of a function.\footnote{cf.~the \ualmodule{Overture.Func.Inverses} module of the \agdaalgebras library.}

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b

\end{code}
An inhabitant of \aod{Image} \ab f \aod{∋} \ab b is a dependent pair \AgdaPair{a}{p},
where \AgdaTyped{a}{A} and \ab p~\as :~\ab b \aofld{≈} \ab f~\ab a is a proof that
\ab f maps \ab a to \ab b.  Since the proof that \ab b
belongs to the image of \ab f is always accompanied by a witness \AgdaTyped{a}{A}, we can
actually \emph{compute} a (pseudo)inverse of \ab f. For convenience, we define this
inverse function, which we call \af{Inv}, and which takes an arbitrary \AgdaTyped{b}{B} and
a (witness, proof)-pair, \AgdaPair{a}{p}~\as :~\aod{Image}~\ab f~\aod{∋}~\ab b, and returns the witness \ab a.

\begin{code}

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p

\end{code}
The latter (\af{InvIsInverseʳ}) proves that \af{Inv} \ab f is the range-restricted right-inverse of the setoid function \ab f.



\paragraph*{Injective and surjective setoid functions}
If \ab{f} : \ab{𝑨} \aor{⟶} \ab{𝑩} is a setoid function from \ab{𝑨} = (\ab{A} \AgdaComma \aofld{≈₀}) to
\ab{𝑩} = (\ab{B} \AgdaComma \aofld{≈₁}), then we call \ab f \emph{injective} provided \as{∀} (\ab{a₀} \ab{a₁} \as : \ab{A}),
\ab{f} \aofld{⟨\$⟩} \ab{a₀} \aofld{≈₁} \ab{f} \aofld{⟨\$⟩} \ab{a₁} implies \ab{a₀} \aofld{≈₀} \ab{a₁};
we call \ab{f} \emph{surjective} provided \as{∀} (\AgdaTyped{b}{B}), \as{∃}~(\AgdaTyped{a}{A}) such that
\ab{f} \aofld{⟨\$⟩} \ab{a} \aofld{≈₁} \ab{b}.
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
The \emph{kernel} of a function \ab f~\as :~\ab A~\as{→}~\ab B (where \ab A and \ab B are bare types) is defined
informally by
\begin{center}
\{\AgdaPair{x}{y} \aod{∈} \ab A \aof{×} \ab A \as : \ab f \ab x \as{=} \ab f \ab y \}.
\end{center}
This can be represented in Agda in a number of ways, but for our purposes it is most
convenient to define the kernel as an inhabitant of a (unary) predicate over the square of
the function's domain, as follows.

\begin{code}

module _ {A : Type α}{B : Type β} where

 kernel : Rel B ρ → (A → B) → Pred (A × A) ρ
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
§\ref{signatures-and-signature-types} defines a general notion of \emph{signature} of a structure and then defines a type that represent signatures;
§§\ref{algebras-and-algebra-types}--\ref{product-algebras} do the same for
for \emph{algebraic structures} and \emph{product algebras}, respectively;
§\ref{homomorphisms} defines \emph{homomorphism}, \emph{monomorphism}, and \emph{epimorphism}, presents types that codify these concepts and formally verifies some of their basic properties;
§§\ref{subalgebras}--\ref{terms} do the same for \emph{subalgebra} and \emph{term}, respectively.


%% -----------------------------------------------------------------------------
\subsection{Signatures and signature types}
\label{signatures-and-signature-types}

In model theory, the \emph{signature} \ab{𝑆} = (\ab{𝐶}, \ab{𝐹}, \ab{𝑅}, \ab{ρ})
of a structure consists of three (possibly empty) sets \ab{𝐶}, \ab{𝐹}, and
\ab{𝑅}---called \emph{constant}, \emph{function}, and
\emph{relation} symbols, respectively---along with a function \ab{ρ} : \ab{𝐶} \as{+}
\ab{𝐹} \as{+} \ab{𝑅} \as{→} \ab{𝑁} that assigns an \emph{arity} to each symbol. Often, but
not always, \ab{𝑁} is taken to be the set of natural numbers.

As our focus here is universal algebra, we are more concerned with the
restricted notion of an \emph{algebraic signature}, that is, a signature for
``purely algebraic'' structures, by which is meant a pair \ab{𝑆} = \AgdaPair{F}{ρ}
consisting of a collection \ab{F} of \emph{operation symbols} and a function
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

module _ where
 open Setoid        using ( _≈_ )
 open IsEquivalence using ( refl ; sym ; trans )

 ⟨_⟩ : Signature 𝓞 𝓥 → Setoid α ρᵃ → Setoid _ _

 Carrier (⟨ 𝑆 ⟩ ξ)              = Σ[ f ∈ ∣ 𝑆 ∣ ] (∥ 𝑆 ∥ f → ξ .Carrier)

 _≈_ (⟨ 𝑆 ⟩ ξ) (f , u) (g , v)  = Σ[ eqv ∈ f ≡ g ] EqArgs{ξ = ξ} eqv u v

 refl   (isEquivalence (⟨ 𝑆 ⟩ ξ))                           = ≡.refl , λ i → Setoid.refl   ξ
 sym    (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)              = ≡.refl , λ i → Setoid.sym    ξ (g i)
 trans  (isEquivalence (⟨ 𝑆 ⟩ ξ)) (≡.refl , g)(≡.refl , h)  = ≡.refl , λ i → Setoid.trans  ξ (g i) (h i)
\end{code}

%% -----------------------------------------------------------------------------
\subsection{Algebras and algebra types}
\label{algebras-and-algebra-types}
Informally, an \emph{algebraic structure in the signature} \ab{𝑆} = (\ab{F}, \ab{ρ}) (or \ab{𝑆}-\emph{algebra}) is denoted by \ab{𝑨} = (\ab{A}, \ab{Fᴬ}) and consists of
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
We now present the definition of the \ar{Algebra} type and explain how the standard library's \ar{Func} type is used to represent the interpretation of operation symbols in an algebra.\footnote{We postpone introducing identities until they are needed (e.g., for equational logic); see~§\ref{model-theory-and-equational-logic}.}
\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field  Domain : Setoid α ρ
        Interp : (⟨ 𝑆 ⟩ Domain) ⟶ Domain

\end{code}
Recall, we renamed Agda's \ar{Func} type, prefering instead the long-arrow symbol \AgdaRecord{⟶}, so
the \afld{Interp} field has type \ar{Func} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain}) \afld{Domain}, a record type with two fields:
\begin{itemize}
\item a function  \ab{f} \as : \afld{Carrier} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain})
  \as{→} \afld{Carrier} \afld{Domain} representing the operation;
\item a proof \afld{cong} \as : \ab f \ao{\af{Preserves}} \ao{\afld{\au{}≈₁\au}} \ao{\ar{⟶}}
  \ao{\afld{\au{}≈₂\au}} that the operation preserves the relevant setoid equalities.
\end{itemize}
Thus, for each operation symbol in the signature \ab{𝑆}, we have a setoid function \ab f---with domain a power of \afld{Domain} and codomain \afld{Domain}---along with a proof that this function respects the setoid equalities.  The latter means that the operation \ab{f} is accompanied by a proof of the following: ∀ \ab u \ab v in \afld{Carrier} (\aof{⟨} \ab{𝑆} \aof{⟩} \afld{Domain}), if \ab u \afld{≈₁} \ab v, then \ab{f} \aofld{⟨\$⟩} \ab{u} \aofld{≈₂} \ab{f} \aofld{⟨\$⟩} \ab{v}.

In the \agdaalgebras library is defined some syntactic sugar that helps to make our formalizations easier to read and
comprehend.
%\footnote{We omit the formal definitions, but see [reference needed].}
The following are three examples of such syntax that we use below: if \ab{𝑨} is an algebra, then
\begin{itemize}
\item \aof{𝔻[ \ab{𝑨} ]} denotes the setoid \afld{Domain} \ab{𝑨},
\item \aof{𝕌[ \ab{𝑨} ]} is the underlying carrier or ``universe'' of the algebra \ab{𝑨}, and
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
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

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

\subsection{Product Algebras}
\label{product-algebras}
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

The following type definition formalizes the foregoing notion of \defn{product algebra} in Martin-Löf type theory.\footnote{cf.~the \ualmodule{Algebras.Func.Products} module of the \agdaalgebras library.}

\begin{code}

module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)
 Domain (⨅ 𝒜) =
  record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
          ; _≈_ = λ a b → ∀ i → (Setoid._≈_ 𝔻[ 𝒜 i ]) (a i)(b i)
          ; isEquivalence =
            record  { refl   = λ i →      IsEquivalence.refl   (isEquivalence 𝔻[ 𝒜 i ])
                    ; sym    = λ x i →    IsEquivalence.sym    (isEquivalence 𝔻[ 𝒜 i ])(x i)
                    ; trans  = λ x y i →  IsEquivalence.trans  (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i) }}
 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong (Interp (𝒜 i)) (≡.refl , flip f=g i )
\end{code}





%% -------------------------------------------------------------------------------------

\subsection{Homomorphisms}
\label{homomorphisms}

\paragraph*{Basic definitions}
\label{homomorphisms-basic-definitions}

Suppose \ab{𝑨} and \ab{𝑩} are \ab{𝑆}-algebras. A \defn{homomorphism} (or
``hom'') from \ab{𝑨} to \ab{𝑩} is a setoid function
\ab{h}~:~\aof{𝔻[ \ab{𝑨} ]} \as{→} \aof{𝔻[ \ab{𝑩} ]} that is \defn{compatible}
(or \defn{commutes}) with all basic operations; that is,
for every operation symbol \ab{f}~:~\af{∣ \ab{𝑆} ∣} and all tuples
\ab{a}~:~\af{∥ \ab{𝑆} ∥}~\ab{f} \as{→} \aof{𝔻[ \ab{𝑨} ]}, the following
equality holds: \ab{h} \aofld{⟨\$⟩} (\ab{f}~\af{̂}~\ab{𝑨}) \ab{a} \aofld{≈}
(\ab{f}~\af{̂}~\ab{𝑩}) \as{λ} \ab{x} \as{→} \ab{h} \aofld{⟨\$⟩} (\ab{a} \ab{x}).

To formalize this concept in Agda, we first define a type \af{compatible-map-op}
representing the assertion that a given setoid function
\ab{h}~:~\aof{𝔻[ \ab{𝑨} ]} \as{→} \aof{𝔻[ \ab{𝑩} ]} commutes with a given
basic operation \ab{f}.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 private ov = 𝓞 ⊔ 𝓥 ; a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = 𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type (𝓥 ⊔ α ⊔ ρᵇ)
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

\end{code}
Generalizing over operation symbols gives the following type of compatible maps
from (the domain of) \ab{𝐴} to (the domain of) \ab{𝑩}.
\begin{code}

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type (ov ⊔ α ⊔ ρᵇ)
 compatible-map h = ∀ {f} → compatible-map-op h f

\end{code}
With this we define a record type \ar{IsHom} representing the property of being
a homomorphism, and finally the type \af{hom} of homomorphisms from \ab{𝑨} to \ab{𝐵}.
\begin{code}

 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ α ⊔ ρᵇ) where
  constructor mkhom
  field compatible : compatible-map h

 hom : Type c
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom
\end{code}

Observe that an inhabitant of \af{hom} is a pair (\ab h , \ab p) whose first component is a setoid function from the domain of \ab{𝑨} to the domain of \ab{𝐵} and whose second component is a proof, \ab p : \ar{IsHom} \ab h, that \ab h is a homomorphism.

A \defn{monomorphism} (resp. \emph{epimorphism}) is an injective (resp. surjective) homomorphism.  The \agdaalgebras library defines types \ar{IsMon} and \ar{IsEpi} to represent these properties, as well as
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

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ a ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h

  HomReduct : hom
  HomReduct = h , isHom

 mon : Type c
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

\end{code}
As with \af{hom}, the type \af{mon} is a dependent product type; each inhabitant is a pair consisting of a setoid function, say, \ab h, along with a proof that \ab h is a monomorphism.

\begin{code}

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (ov ⊔ α ⊔ b) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h

  HomReduct : hom
  HomReduct = h , isHom

 epi : Type c
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
\end{code}
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%
%%%
%%% BEGIN NO VERSION SECTION (the next block of code will appear in neither version of the paper)
%%%
\begin{code}[hide]
open IsHom ; open IsMon ; open IsEpi

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
\end{code}
%%%
%%% END NO VERSION SECTION
%%%


%\subsubsection*{Basic properties of homomorphisms}
%Some definitions and theorems extracted from the \ualmodule{Homomorphisms.Func.Properties} module of the \agdaalgebras library.

\paragraph*{Composition of homomorphisms} The composition of homomorphisms is again a homomorphism. Similarly,
the composition of epimorphisms is again an epimorphism.

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
\end{code}
\ifshort\else
         %%%
         %%% BEGIN LONG VERSION ONLY SECTION
         %%%
\begin{code}

module _ {𝑨 : Algebra α ρᵃ} {𝑩 : Algebra β ρᵇ} {𝑪 : Algebra γ ρᶜ} where

  ∘-hom : hom 𝑨 𝑩 → hom 𝑩 𝑪  → hom 𝑨 𝑪
  ∘-hom (h , hhom) (g , ghom) = (g ⟨∘⟩ h) , ∘-is-hom hhom ghom

  ∘-epi : epi 𝑨 𝑩 → epi 𝑩 𝑪  → epi 𝑨 𝑪
  ∘-epi (h , hepi) (g , gepi) = (g ⟨∘⟩ h) , ∘-is-epi hepi gepi
\end{code}

\paragraph*{Universe lifting of homomorphisms} First we define the identity homomorphism for setoid algebras and then we prove that the operations of lifting and lowering of a setoid algebra are homomorphisms.

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
Suppose we have an algebra \ab{𝑨}, a type \ab I : \apr{Type} \ab 𝓘, and a family \ab ℬ : \ab I \as → \ar{Algebra} \ab β \ab{𝑆} of algebras.
We sometimes refer to the inhabitants of `I` as \emph{indices}, and call `ℬ` an \emph{indexed family of algebras}.
If in addition we have a family `𝒽 : (i : I) → hom 𝑨 (ℬ i)` of homomorphisms, then we can construct a homomorphism from `𝑨` to the product `⨅ ℬ` in the natural way.  Here is how we implement these notions in dependent type theory.\footnote{cf.~the [Homomorphisms.Func.Products][] module of the \agdaalgebras library.}

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
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%

\paragraph*{Factorization of homomorphisms} If \ab g : \af{hom} \ab{𝑨} \ab{𝑩}, \ab h : \af{hom} \ab{𝑨} \ab{𝑪}, \ab h is
surjective, and \af{ker} \ab h \aof{⊆} \af{ker} \ab g, then there exists
\ab{φ} : \af{hom} \ab{𝑪} \ab{𝑩} such that \ab g = \ab{φ} \aof{∘} \ab h.

         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
Here we merely give the formal statement of this theorem, but \seeunabridged or the
\ualmodule{Homomorphisms.Func.Factor} module of the \agdaalgebras library.
         %%%
\else\fi %%% END SHORT VERSION ONLY

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ){𝑪 : Algebra γ ρᶜ}
         (gh : hom 𝑨 𝑩)(hh : hom 𝑨 𝑪) where
 open Setoid 𝔻[ 𝑩 ] using ()         renaming ( _≈_ to _≈₂_ ; sym to sym₂ )
 open Setoid 𝔻[ 𝑪 ] using ( trans )  renaming ( _≈_ to _≈₃_ ; sym to sym₃ )
 private gfunc = ∣ gh ∣ ; g = _⟨$⟩_ gfunc ; hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 HomFactor :  kernel _≈₃_ h ⊆ kernel _≈₂_ g → IsSurjective hfunc
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

  ζ : ∀{x y} → x ≈₃ y → h (h⁻¹ x) ≈₃ h (h⁻¹ y)
  ζ xy = trans η (trans xy (sym₃ η))

  φmap : 𝔻[ 𝑪 ] ⟶ 𝔻[ 𝑩 ]
  _⟨$⟩_ φmap = g ∘ h⁻¹
  cong φmap = Khg ∘ ζ
  open _⟶_ φmap using () renaming (cong to φcong)

  gφh : (a : 𝕌[ 𝑨 ]) → g a ≈₂ φmap ⟨$⟩ h a
  gφh a = Khg (sym₃ η)

  open SetoidReasoning 𝔻[ 𝑩 ]
  φcomp : compatible-map 𝑪 𝑩 φmap
  φcomp {f}{c} =
   begin
    φmap ⟨$⟩  (f ̂ 𝑪)                   c       ≈˘⟨  φcong (cong (Interp 𝑪) (≡.refl , λ _ → η))  ⟩
    g(h⁻¹(    (f ̂ 𝑪)  (h ∘    h⁻¹  ∘  c  )))   ≈˘⟨  φcong (compatible ∥ hh ∥)                   ⟩
    g(h⁻¹(h(  (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))))  ≈˘⟨  gφh ((f ̂ 𝑨)(h⁻¹ ∘ c))                      ⟩
    g(        (f ̂ 𝑨)  (       h⁻¹  ∘  c  ))    ≈⟨   compatible ∥ gh ∥                           ⟩
              (f ̂ 𝑩)  (g ∘ (  h⁻¹  ∘  c  ))    ∎

  φhom : IsHom 𝑪 𝑩 φmap
  compatible φhom = φcomp
\end{code}
         %%%
\fi      %%% END LONG VERSION ONLY SECTION
         %%%


\paragraph*{Isomorphisms}
%\label{isomorphisms}

Two structures are \emph{isomorphic} provided there are homomorphisms going back and forth between them which compose to the identity map.

         %%%
\ifshort %%% BEGIN SHORT VERSION ONLY
         %%%
The \agdaalgebras library's \ar{\au{}≅\au{}} type codifies the definition of isomorphism, as well as some obvious consequences.  Here we display only the core part of this record type, but \seeunabridged or the \ualmodule{Homomorphisms.Func.Isomorphisms} module of the \agdaalgebras library.
         %%%
\else\fi %%% END SHORT VERSION ONLY
         %%%

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; sym ; trans )
 open Setoid 𝔻[ 𝑩 ] using () renaming ( _≈_ to _≈ᴮ_ ; sym to symᵇ ; trans to transᵇ)

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ ) where
  constructor mkiso
  field
   to : hom 𝑨 𝑩
   from : hom 𝑩 𝑨
   to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
   from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ a
\end{code}
\ifshort %%%
\else    %%% BEGIN LONG VERSION ONLY
         %%%
\begin{code}

  toIsSurjective : IsSurjective ∣ to ∣
  toIsSurjective {y} = eq (∣ from ∣ ⟨$⟩ y) (symᵇ (to∼from y))

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x} {y} xy = Goal
   where
   ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
   ξ = cong ∣ from ∣ xy
   Goal : x ≈ y
   Goal = trans (sym (from∼to x)) (trans ξ (from∼to y))

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {y} = eq (∣ to ∣ ⟨$⟩ y) (sym (from∼to y))

  fromIsInjective : IsInjective ∣ from ∣
  fromIsInjective {x} {y} xy = Goal
   where
   ξ : ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ x) ≈ᴮ ∣ to ∣ ⟨$⟩ (∣ from ∣ ⟨$⟩ y)
   ξ = cong ∣ to ∣ xy
   Goal : x ≈ᴮ y
   Goal = transᵇ (symᵇ (to∼from x)) (transᵇ ξ (to∼from y))

open _≅_
\end{code}

\begin{code}

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )

≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ})(_≅_{β}{ρᵇ})(_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν
 where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; trans )
  open Setoid 𝔻[ 𝑪 ] using () renaming ( _≈_ to _≈ᶜ_ ; trans to transᶜ )
  f : hom 𝑨 𝑪
  f = ∘-hom (to ab) (to bc)
  g : hom 𝑪 𝑨
  g = ∘-hom (from bc) (from ab)
  τ : ∀ b → ∣ f ∣ ⟨$⟩ (∣ g ∣ ⟨$⟩ b) ≈ᶜ b
  τ b = transᶜ (cong ∣ to bc ∣ (to∼from ab (∣ from bc ∣ ⟨$⟩ b))) (to∼from bc b)
  ν : ∀ a → ∣ g ∣ ⟨$⟩ (∣ f ∣ ⟨$⟩ a) ≈ a
  ν a = trans (cong ∣ from ab ∣ (from∼to bc (∣ to ab ∣ ⟨$⟩ a))) (from∼to ab a)

\end{code}

Fortunately, the lift operation preserves isomorphism (i.e., it's an \emph{algebraic invariant}). As our focus is universal algebra, this is important and is what makes the lift operation a workable solution to the technical problems that arise from the noncumulativity of Agda's universe hierarchy.

\begin{code}[hide]
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

\paragraph*{Homomorphic Images}
%\label{homomorphic-images}
We begin with what for our purposes is the most useful way to represent the class of \emph{homomorphic images} of an algebra in dependent type theory.\footnote{cf.~the \ualmodule{Homomorphisms.Func.HomomorphicImages} module of the \agdaalgebras library.}

\begin{code}
ov : Level → Level
ov α = 𝓞 ⊔ 𝓥 ⊔ lsuc α

_IsHomImageOf_ : (𝑩 : Algebra β ρᵇ)(𝑨 : Algebra α ρᵃ) → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵃ ⊔ ρᵇ)
𝑩 IsHomImageOf 𝑨 = Σ[ φ ∈ hom 𝑨 𝑩 ] IsSurjective ∣ φ ∣

HomImages : Algebra α ρᵃ → Type (α ⊔ ρᵃ ⊔ ov (β ⊔ ρᵇ))
HomImages {β = β}{ρᵇ = ρᵇ} 𝑨 = Σ[ 𝑩 ∈ Algebra β ρᵇ ] 𝑩 IsHomImageOf 𝑨

\end{code}
These types should be self-explanatory, but just to be sure, let's describe the
Sigma type appearing in the second definition. Given an \ab{𝑆}-algebra \ab{𝑨} :
\ar{Algebra} \ab{α} \ab{ρ}, the type \af{HomImages} \ab{𝑨} denotes the class of
algebras \ab{𝑩} : \ar{Algebra} \ab{β} \ab{ρ} with a map \ab{φ} : \aof{∣} \ab{𝑨}
\aof{∣} \as{→} \aof{∣} \ab{𝑩} \aof{∣} such that \ab{φ} is a surjective
homomorphism.

\begin{code}[hide]
module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 Lift-HomImage-lemma : ∀{γ} → (Lift-Alg 𝑨 γ γ) IsHomImageOf 𝑩 → 𝑨 IsHomImageOf 𝑩
 Lift-HomImage-lemma {γ} φ = ∘-hom ∣ φ ∣ (from Lift-≅) ,
                             ∘-IsSurjective _ _ ∥ φ ∥ (fromIsSurjective (Lift-≅{𝑨 = 𝑨}))

module _ {𝑨 𝑨' : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 HomImage-≅ : 𝑨 IsHomImageOf 𝑨' → 𝑨 ≅ 𝑩 → 𝑩 IsHomImageOf 𝑨'
 HomImage-≅ φ A≅B = ∘-hom ∣ φ ∣ (to A≅B) , ∘-IsSurjective _ _ ∥ φ ∥ (toIsSurjective A≅B)
\end{code}




%% -------------------------------------------------------------------------------------

\subsection{Subalgebras}
\label{subalgebras}
\paragraph*{Basic definitions}
%\label{subalgebras-basic-definitions}

\begin{code}

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
\end{code}

\paragraph*{Basic properties}
%\label{subalgebras-basic-properties}

\begin{code}

≤-reflexive : {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive {𝑨 = 𝑨} = 𝒾𝒹 , id

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} where
 ≤-trans : 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≤-trans ( f , finj ) ( g , ginj ) = (∘-hom f g ) , ∘-IsInjective ∣ f ∣ ∣ g ∣ finj ginj

 ≅-trans-≤ : 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
 ≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-IsInjective ∣ to A≅B ∣ ∣ h ∣ (toIsInjective A≅B) hinj)
\end{code}

\paragraph*{Products of subalgebras}
%\label{products-of-subalgebras}

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




%% -------------------------------------------------------------------------------------

\subsection{Terms}
\label{terms}
\paragraph*{Basic definitions}
Fix a signature \ab{𝑆} and let \ab X denote an arbitrary nonempty collection of variable symbols. Assume the symbols in \ab X are distinct from the operation symbols of \ab{𝑆}, that is \ab X \aof{∩} \aof{∣} \ab{𝑆} \aof{∣} = ∅.
By a \emph{word} in the language of \ab{𝑆}, we mean a nonempty, finite sequence of members of \ab X \aof{∪} \aof{∣} \ab{𝑆} \aof{∣}. We denote the concatenation of such sequences by simple juxtaposition.
Let \ab{S₀} denote the set of nullary operation symbols of \ab{𝑆}. We define by induction on \ab n the sets \ab{𝑇ₙ} of \emph{words} over \ab X \aof{∪} \aof{∣} \ab{𝑆} \aof{∣} as follows (cf.~\cite[Def. 4.19]{Bergman:2012}):
\begin{enumerate}
\item \ab{𝑇₀} := \ab X \aof{∪} \ab{S₀}, and
\item \ab{𝑇ₙ₊₁} := \ab{𝑇ₙ} \aof{∪} \ab{𝒯ₙ}.
\end{enumerate}
where \ab{𝒯ₙ} is the collection of all \ab f \ab t such that \ab f : \aof{∣} \ab{𝑆} \aof{∣} and \ab t : \aof{∥} \ab{𝑆} \aof{∥} \ab f \as{→} \ab{𝑇ₙ}. (Recall, \aof{∥} \ab{𝑆} \aof{∥} \ab f is the arity of the operation symbol \ab f.)

We define the collection of \emph{terms} in the signature \ab{𝑆} over \ab X by \ad{Term} \ab X := \aof{⋃ₙ} \ab{𝑇ₙ}. By an 𝑆-\emph{term} we mean a term in the language of \ab{𝑆}.

The definition of \ad{Term} \ab X is recursive, indicating that an inductive type could be used to represent the semantic notion of terms in type theory. Indeed, such a representation is given by the following inductive type.

\begin{code}

data Term (X : Type χ ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X
open Term

\end{code}

This is a very basic inductive type that represents each term as a tree with an operation symbol at each \aic{node} and a variable symbol at each leaf (\aic{ℊ}); hence the constructor names (\aic{ℊ} for ``generator'' and \aic{node} for ``node'').

\textbf{Notation}. As usual, the type \ab X represents an arbitrary collection of variable symbols. Recall, \af{ov} \ab{χ} is our shorthand notation for the universe level \ab{𝓞} \aop{⊔} \ab{𝓥} \aop{⊔} \ap{lsuc} \ab{χ}.
\paragraph*{Equality of terms}
%\label{equality-of-terms}
We take a different approach here, using Setoids instead of quotient types.
That is, we will define the collection of terms in a signature as a setoid
with a particular equality-of-terms relation, which we must define.
Ultimately we will use this to define the (absolutely free) term algebra
as a Algebra whose carrier is the setoid of terms.

\begin{code}

module _ {X : Type χ } where

 data _≐_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≐ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≐ (t i)) → (node f s) ≐ (node f t)

\end{code}

It is easy to show that the equality-of-terms relation \AgdaOperator{\AgdaDatatype{\AgdaUnderscore{}≐\AgdaUnderscore{}}} is an equivalence relation, so we omit the formal proof. (See the \ualmodule{Terms.Func.Basic} module of the \agdaalgebras library for details.)

\begin{code}[hide]
 ≐-isRefl : Reflexive _≐_
 ≐-isRefl {ℊ _} = rfl ≡.refl
 ≐-isRefl {node _ _} = gnl (λ _ → ≐-isRefl)

 ≐-isSym : Symmetric _≐_
 ≐-isSym (rfl x) = rfl (≡.sym x)
 ≐-isSym (gnl x) = gnl (λ i → ≐-isSym (x i))

 ≐-isTrans : Transitive _≐_
 ≐-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≐-isTrans (gnl x) (gnl y) = gnl (λ i → ≐-isTrans (x i) (y i))

 ≐-isEquiv : IsEquivalence _≐_
 ≐-isEquiv = record { refl = ≐-isRefl ; sym = ≐-isSym ; trans = ≐-isTrans }
\end{code}


\paragraph*{The term algebra}
%\label{the-term-algebra}
For a given signature \ab{𝑆}, if the type \ad{Term} \ab X is nonempty
(equivalently, if \ab X or \aof{∣} \ab{𝑆} \aof{∣} is nonempty), then we can
define an algebraic structure, denoted by \T{X} and called the \emph{term
  algebra in the signature} \ab{𝑆} \emph{over} \ab X.  Terms are viewed as
acting on other terms, so both the domain and basic operations of the algebra
are the terms themselves.


\begin{itemize}
\item For each operation symbol \ab f : \aof{∣} \ab{𝑆} \aof{∣}, denote by \ab f
  \aof{̂} (\T{X}) the operation on \ad{Term} \ab X that maps a tuple \ab t :
  \aof{∥} \ab{𝑆} \aof{∥} \ab f \as{→} \aof{∣} \T{X} \aof{∣} to the formal term \ab f \ab t.
\item Define \T{X} to be the algebra with universe \aof{∣} \T{X} \aof{∣} :=
  \ad{Term} \ab X and operations \ab f \aof{̂} (\T{X}), one for each symbol
  \ab f in \aof{∣} \ab{𝑆} \aof{∣}.
\end{itemize}

In \agda the term algebra can be defined as simply as one might hope.

\begin{code}

TermSetoid : (X : Type χ) → Setoid (ov χ) (ov χ)
TermSetoid X = record { Carrier = Term X ; _≈_ = _≐_ ; isEquivalence = ≐-isEquiv }

𝑻 : (X : Type χ) → Algebra (ov χ) (ov χ)
Algebra.Domain (𝑻 X) = TermSetoid X
Algebra.Interp (𝑻 X) ⟨$⟩ (f , ts) = node f ts
cong (Algebra.Interp (𝑻 X)) (≡.refl , ss≐ts) = gnl ss≐ts
\end{code}

\paragraph*{Interpretation of terms}
%\label{interpretation-of-terms}

The approach to terms and their interpretation in this module was inspired by
Andreas Abel's formal proof of Birkhoff's completeness theorem.\footnote{See \abel.}

A substitution from \ab X to \ab Y associates a term in \ab X with each variable in \ab Y.  The definition of \af{Sub} given here is essentially the same as the one given by Andreas Abel, as is the recursive definition of the syntax \ab t \af{[} \ab{σ} \af{]} , which denotes a term \ab t applied to a substitution \ab{σ}.

\begin{code}

Sub : Type χ → Type χ → Type (ov χ)
Sub X Y = (y : Y) → Term X

_[_] : {X Y : Type χ}(t : Term Y) (σ : Sub X Y) → Term X
(ℊ x) [ σ ] = σ x
(node f ts) [ σ ] = node f (λ i → ts i [ σ ])

\end{code}

An environment for an algebra \ab{𝑨} in a context \ab X is a map that assigns to each variable \AgdaTyped{x}{X} an element in the domain of \ab{𝑨}, packaged together with an equality of environments, which is simply pointwise equality (relatively to the setoid equality of the underlying domain of \ab{𝑨}).

\begin{code}

module Environment (𝑨 : Algebra α ℓ) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; refl ; sym ; trans )
 Env : Type χ → Setoid _ _
 Env X = record  { Carrier = X → 𝕌[ 𝑨 ]
                 ; _≈_ = λ ρ ρ' → (x : X) → ρ x ≈ ρ' x
                 ; isEquivalence = record  { refl   = λ _ → refl
                                           ; sym    = λ h x → sym (h x)
                                           ; trans  = λ g h x → trans (g x)(h x) }}

\end{code}

Next we define \emph{evaluation of a term} in an environment \ab{ρ}, interpreted in the algebra \ab{𝑨}.

\begin{code}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v = u≈v x
 cong ⟦ node f args ⟧ x≈y = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}

An equality between two terms holds in a model if the two terms are equal under all valuations of their free variables.\footnote{cf.~Andreas Abel's formal proof of Birkhoff's completeness theorem [reference needed].}

\begin{code}

 Equal : ∀ {X : Type χ} (s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) →  ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

 ≐→Equal : {X : Type χ}(s t : Term X) → s ≐ t → Equal s t
 ≐→Equal .(ℊ _) .(ℊ _) (rfl ≡.refl) = λ _ → refl
 ≐→Equal (node _ s)(node _ t)(gnl x) =
  λ ρ → cong (Interp 𝑨)(≡.refl , λ i → ≐→Equal(s i)(t i)(x i)ρ )

\end{code}

The proof that \af{Equal} is an equivalence relation is trivial, so we omit it. (See the \ualmodule{Varieties.Func.SoundAndComplete} module of the \agdaalgebras library for details.)

\begin{code}[hide]
 EqualIsEquiv : {Γ : Type χ} → IsEquivalence (Equal {X = Γ})
 IsEquivalence.refl  EqualIsEquiv = λ _ → refl
 IsEquivalence.sym   EqualIsEquiv = λ x=y ρ → sym (x=y ρ)
 IsEquivalence.trans EqualIsEquiv = λ ij jk ρ → trans (ij ρ) (jk ρ)
\end{code}

Evaluation of a substitution gives an environment.\footnote{cf.~Andreas Abel's formal proof of Birkhoff's completeness theorem [reference needed].}
%(http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf))

\begin{code}

 ⟦_⟧s : {X Y : Type χ} → Sub X Y → Carrier(Env X) → Carrier (Env Y)
 ⟦ σ ⟧s ρ x = ⟦ σ x ⟧ ⟨$⟩ ρ

\end{code}

Next we prove that \aof{⟦} \ab{t} \af{[} \ab{σ} \af{]} \aof{⟧} \ab{ρ} ≃ \aof{⟦} \ab t \aof{⟧} \aof{⟦} \ab{σ} \aof{⟧} \ab{ρ}.
%(cf. Andreas Abel's formal proof of Birkhoff's completeness theorem).

\begin{code}

 substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
  →              ⟦ t [ σ ] ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ⟦ σ ⟧s ρ

 substitution (ℊ x)        σ ρ = refl
 substitution (node f ts)  σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)
\end{code}


\paragraph*{Compatibility of terms}
%\label{compatibility-of-terms}
We now prove two important facts about term operations.  The first of these, which is used very often in the sequel, asserts that every term commutes with every homomorphism.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Setoid 𝔻[ 𝑩 ] using ( _≈_ ; refl )
 open SetoidReasoning 𝔻[ 𝑩 ]
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc
 open Environment 𝑨 using ( ⟦_⟧ )
 open Environment 𝑩 using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a = goal
  where
  goal : h (⟦ node f t ⟧ ⟨$⟩ a) ≈ ⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a)
  goal = begin
          h (  ⟦ node f t ⟧           ⟨$⟩         a  )  ≈⟨  compatible ∥ hh ∥                                     ⟩
          (f ̂ 𝑩)( λ i → h(  ⟦ t i ⟧   ⟨$⟩         a) )  ≈⟨  cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term (t i) a)  ⟩
          (f ̂ 𝑩)( λ i →     ⟦ t i ⟧ᴮ  ⟨$⟩  (h  ∘  a) )  ≈⟨  refl                                                  ⟩
               ⟦ node f t ⟧ᴮ          ⟨$⟩  (h  ∘  a)    ∎
\end{code}

%% \subsection{Interpretation of terms in product algebras}
%% a id="interpretation-of-terms-in-product-algebras">

\begin{code}[hide]
module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
 open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
 open Environment        using ( ⟦_⟧ ; ≐→Equal )

 interp-prod : (p : Term X) → ∀ ρ → ⟦ p ⟧₁ ⟨$⟩ ρ ≈ λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x) = λ ρ i → ≐→Equal (𝒜 i) (ℊ x) (ℊ x) ≐-isRefl λ _ → (ρ x) i
 interp-prod (node f t) = λ ρ → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )
\end{code}





%% -------------------------------------------------------------------------------------

\section{Model Theory and Equational Logic}
\label{model-theory-and-equational-logic}

(cf. the \ualmodule{Varieties.Func.SoundAndComplete} module of the \agdaalgebras library)

\subsection{Basic definitions}
\label{model-theory-basic-definitions}

Let \ab{𝑆} be a signature. By an \emph{identity} or \emph{equation} in \ab{𝑆} we mean an ordered pair of terms in a given context.  For instance, if the context happens to be the type \ab X : \ap{Type} \ab{χ}, then an equation will be a pair of inhabitants of the domain of term algebra \af{𝑻} \ab X.

We define an equation in Agda using the following record type with fields denoting the left-hand and right-hand sides of the equation, along with an equation ``context'' representing the underlying collection of variable symbols.\footnote{cf.~Andreas Abel's formal proof of Birkhoff's completeness theorem [reference needed].}

\begin{code}

record Eq : Type (ov χ) where
 constructor _≈̇_
 field  {cxt}  : Type χ
        lhs    : Term cxt
        rhs    : Term cxt

open Eq public

\end{code}

We now define a type representing the notion of an equation \ab p \aoic{≈̇} \ab q holding (when \ab p and \ab q are interpreted) in algebra \ab{𝑨}.

If \ab{𝑨} is an \ab{𝑆}-algebra we say that \ab{𝑨} \emph{satisfies} \ab p \aofld{≈} \ab q provided for all environments \ab{ρ} : \ab X \as{→} \aof{∣} \ab{𝑨} \aof{∣} (assigning values in the domain of \ab{𝑨} to variable symbols in \ab X) we have \aof{⟦} \ab p \aof{⟧} \aofld{⟨\$⟩} \ab{ρ} \aofld{≈} \aof{⟦} \ab q \aof{⟧} \aofld{⟨\$⟩} \ab{ρ}.  In this situation, we write \ab{𝑨} \aof{⊧} (\ab p \aoic{≈̇} \ab q) and say that \ab{𝑨} \emph{models} the identity \ab p \aofld{≈} \ab q.

If \ab{𝒦} is a class of algebras, all of the same signature, we write \ab{𝒦} \aof{⊫} (\ab p \aoic{≈̇} \ab q) if, for every \ab{𝑨} \aof{∈} \ab{𝒦}, we have \ab{𝑨} \aof{⊧} (\ab p \aoic{≈̇} \ab q).

Because a class of structures has a different type than a single structure, we must use a slightly different syntax to avoid overloading the relations \aof{⊧} and \aofld{≈}. As a reasonable alternative to what we would normally express informally as \ab{𝒦} \aof{⊧} \ab p \aofld{≈} \ab q, we have settled on \ab{𝒦} \aof{⊫} (\ab p \aoic{≈̇} \ab q) to denote this relation.  To reiterate, if \ab{𝒦} is a class of \ab{𝑆}-algebras, we write \ab{𝒦} \aof{⊫} (\ab p \aoic{≈̇} \ab q) provided every \ab{𝑨} \aof{∈} \ab{𝒦} satisfies \ab{𝑨} \aof{⊧} (\ab p \aoic{≈̇} \ab q).

\begin{code}

_⊧_ : (𝑨 : Algebra α ρᵃ)(term-identity : Eq{χ}) → Type _
𝑨 ⊧ (p ≈̇ q) = Equal p q where open Environment 𝑨

_⊫_ : Pred (Algebra α ρᵃ) ℓ → Eq{χ} → Type (ℓ ⊔ χ ⊔ ov(α ⊔ ρᵃ))
𝒦 ⊫ equ = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ equ

\end{code}

We denote by \ab{𝑨} \aof{⊨} \ab{ℰ} the assertion that the algebra \ab{𝑨} models every equation in a collection \ab{ℰ} of equations.

\begin{code}

_⊨_ : (𝑨 : Algebra α ρᵃ) → {ι : Level}{I : Type ι} → (I → Eq{χ}) → Type _
𝑨 ⊨ ℰ = ∀ i → Equal (lhs (ℰ i))(rhs (ℰ i)) where open Environment 𝑨
\end{code}

\subsection{Equational theories and models}
\label{equational-theories-and-models}

If \ab{𝒦} denotes a class of structures, then \af{Th} \ab{𝒦} represents the set of identities
modeled by the members of \ab{𝒦}.

\begin{code}

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ (p ≈̇ q)

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
\end{code}

\subsection{The entailment relation}
\label{the-entailment-relation}

Based on Andreas Abel's Agda formalization of Birkhoff's completeness theorem.

\begin{code}

module _ {χ ι : Level} where

 data _⊢_▹_≈_ {I : Type ι}(ℰ : I → Eq) : (X : Type χ)(p q : Term X) → Type (ι ⊔ ov χ) where
  hyp : ∀ i → let p ≈̇ q = ℰ i in ℰ ⊢ _ ▹ p ≈ q
  app : ∀ {ps qs} → (∀ i → ℰ ⊢ Γ ▹ ps i ≈ qs i) → ℰ ⊢ Γ ▹ (node 𝑓 ps) ≈ (node 𝑓 qs)
  sub : ∀ {p q} → ℰ ⊢ Δ ▹ p ≈ q → ∀ (σ : Sub Γ Δ) → ℰ ⊢ Γ ▹ (p [ σ ]) ≈ (q [ σ ])

  ⊢refl   : ∀ {p}               → ℰ ⊢ Γ ▹ p ≈ p
  ⊢sym    : ∀ {p q : Term Γ}    → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ p
  ⊢trans  : ∀ {p q r : Term Γ}  → ℰ ⊢ Γ ▹ p ≈ q → ℰ ⊢ Γ ▹ q ≈ r → ℰ ⊢ Γ ▹ p ≈ r

 ⊢▹≈IsEquiv : {X : Type χ}{I : Type ι}{ℰ : I → Eq} → IsEquivalence (ℰ ⊢ X ▹_≈_)
 ⊢▹≈IsEquiv = record { refl = ⊢refl ; sym = ⊢sym ; trans = ⊢trans }
\end{code}

\subsection{Soundness}
\label{soundness}

In any model \ab{𝑨} of the equations \ab{ℰ} derived equality is actual equality.\footnote{cf.~Andreas Abel's Agda formalization of Birkhoff's completeness theorem [ref needed].}

\begin{code}

module Soundness  {χ α ι : Level}{I : Type ι} (ℰ : I → Eq{χ})
                  (𝑨 : Algebra α ρᵃ)     -- We assume an algebra 𝑨
                  (V : 𝑨 ⊨ ℰ)            -- that models all equations in ℰ.
                  where

 open SetoidReasoning 𝔻[ 𝑨 ]
 open Environment 𝑨
 open IsEquivalence using ( refl ; sym ; trans )

 sound : ∀ {p q} → ℰ ⊢ Γ ▹ p ≈ q → 𝑨 ⊧ (p ≈̇ q)
 sound (hyp i) = V i
 sound (app es) ρ = cong (Interp 𝑨) (≡.refl , λ i → sound (es i) ρ)
 sound (sub {p = p}{q} Epq σ) ρ =
  begin
   ⟦ p  [ σ ]  ⟧ ⟨$⟩         ρ  ≈⟨   substitution p σ ρ    ⟩
   ⟦ p         ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ  ≈⟨   sound Epq (⟦ σ ⟧s ρ)  ⟩
   ⟦ q         ⟧ ⟨$⟩ ⟦ σ ⟧s  ρ  ≈˘⟨  substitution q σ ρ    ⟩
   ⟦ q  [ σ ]  ⟧ ⟨$⟩         ρ  ∎
 sound (⊢refl   {p = p}                 ) = refl   EqualIsEquiv {x = p}
 sound (⊢sym    {p = p}{q}     Epq      ) = sym    EqualIsEquiv {x = p}{q}     (sound Epq)
 sound (⊢trans  {p = p}{q}{r}  Epq Eqr  ) = trans  EqualIsEquiv {i = p}{q}{r}  (sound Epq)(sound Eqr)
\end{code}


\subsection{The Closure Operators H, S, P and V}
\label{the-closure-operators-h-s-p-and-v}

Fix a signature \ab{𝑆}, let \ab{𝒦} be a class of \ab{𝑆}-algebras, and define

\begin{itemize}
\item \af H \ab{𝒦} = algebras isomorphic to a homomorphic image of a member of \ab{𝒦};
\item \af S \ab{𝒦} = algebras isomorphic to a subalgebra of a member of \ab{𝒦};
\item \af P \ab{𝒦} = algebras isomorphic to a product of members of \ab{𝒦}.
\end{itemize}

A straight-forward verification confirms that \af H, \af S, and \ab P are \emph{closure operators} (expansive, monotone, and idempotent).  A class \ab{𝒦} of \ab{𝑆}-algebras is said to be \emph{closed under the taking of homomorphic images} provided \af H \ab{𝒦} \aof{⊆} \ab{𝒦}. Similarly, \ab{𝒦} is \emph{closed under the taking of subalgebras} (resp., \emph{arbitrary products}) provided \af S \ab{𝒦} \aof{⊆} \ab{𝒦} (resp., \af P \ab{𝒦} \aof{⊆} \ab{𝒦}). The operators \af H, \af S, and \af P can be composed with one another repeatedly, forming yet more closure operators.

An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic. Thus, the class \af H \ab{𝒦} (resp., \af S \ab{𝒦}; resp., \af P \ab{𝒦}) is closed under isomorphism.

A \emph{variety} is a class of \ab{𝑆}-algebras that is closed under the taking of
homomorphic images, subalgebras, and arbitrary products.  To represent varieties
we define types for the closure operators \af H, \af S, and \af P that are composable.
Separately, we define a type \af V which represents closure under all three
operators, \af H, \af S, and \af P.  Thus, if \ab{𝒦} is a class of \ab{𝑆}-algebras`, then 
\af V \ab{𝒦} := \af H (\af S (\af P \ab{𝒦})), and \ab{𝒦} is a variety iff \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.

We now define the type \af H to represent classes of algebras that include all homomorphic images of algebras in the class---i.e., classes that are closed under the taking of homomorphic images---the type \af S to represent classes of algebras that closed under the taking of subalgebras, and the type \af P to represent classes of algebras closed under the taking of arbitrary products.

\begin{code}

module _  {α ρᵃ β ρᵇ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ

 H : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 H _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 IsHomImageOf 𝑨

 S : ∀ ℓ → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ))
 S _ 𝒦 𝑩 = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × 𝑩 ≤ 𝑨

 P : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) → Pred(Algebra β ρᵇ) (b ⊔ ov(a ⊔ ℓ ⊔ ι))
 P _ ι 𝒦 𝑩 = Σ[ I ∈ Type ι ] (Σ[ 𝒜 ∈ (I → Algebra α ρᵃ) ] (∀ i → 𝒜 i ∈ 𝒦) × (𝑩 ≅ ⨅ 𝒜))

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ ; c = γ ⊔ ρᶜ ; d = δ ⊔ ρᵈ

 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) (d ⊔ ov(a ⊔ b ⊔ c ⊔ ℓ ⊔ ι))
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))
\end{code}
\begin{code}[hide]
module _ {α ρᵃ ℓ : Level}(𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ))
         (𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)) where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 V-≅-lc : Lift-Alg 𝑨 ι ι ∈ V{β = ι}{ι} ℓ ι 𝒦 → 𝑨 ∈ V{γ = ι}{ι} ℓ ι 𝒦
 V-≅-lc (𝑨' , spA' , lAimgA') = 𝑨' , (spA' , AimgA')
  where
  AimgA' : 𝑨 IsHomImageOf 𝑨'
  AimgA' = Lift-HomImage-lemma lAimgA'
\end{code}


\paragraph*{Idempotence of S} \af S is a closure operator.  The facts that \af S is monotone and expansive won't be needed, so we omit the proof of these facts.  However, we will make use of idempotence of \af S, so we prove that property as follows.

\begin{code}

S-idem : {𝒦 : Pred (Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}
 →       S{β = γ}{ρᶜ} (α ⊔ ρᵃ  ⊔ ℓ) (S{β = β}{ρᵇ} ℓ 𝒦) ⊆ S{β = γ}{ρᶜ} ℓ 𝒦

S-idem (𝑨 , (𝑩 , sB , A≤B) , x≤A) = 𝑩 , (sB , ≤-trans x≤A A≤B)
\end{code}

\paragraph*{Algebraic invariance of ⊧}
The binary relation \aof{⊧} would be practically useless if it were not an \emph{algebraic invariant} (i.e., invariant under isomorphism). Let us now verify that the models relation we defined above has this essential property.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where

 ⊧-I-invar : 𝑨 ⊧ (p ≈̇ q)  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ (p ≈̇ q)
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ =
  begin
   ⟦ p ⟧₂    ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧₂ (f∼g ∘ ρ)       ⟩
   ⟦ p ⟧₂    ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
   f(⟦ p ⟧₁  ⟨$⟩        (g  ∘  ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
   f(⟦ q ⟧₁  ⟨$⟩        (g  ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
   ⟦ q ⟧₂    ⟨$⟩ (f  ∘  (g  ∘  ρ))  ≈⟨   cong ⟦ q ⟧₂ (f∼g ∘ ρ)       ⟩
   ⟦ q ⟧₂    ⟨$⟩               ρ    ∎
  where
  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
  open Environment 𝑨     using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment 𝑩     using () renaming ( ⟦_⟧ to ⟦_⟧₂ )
  open SetoidReasoning 𝔻[ 𝑩 ]
\end{code}

\paragraph*{Subalgebraic invariance of ⊧}
Identities modeled by an algebra \ab{𝑨} are also modeled by every subalgebra of \ab{𝑨}, which fact can be formalized as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where

 ⊧-S-invar : 𝑨 ⊧ (p ≈̇ q) →  𝑩 ≤ 𝑨  →  𝑩 ⊧ (p ≈̇ q)
 ⊧-S-invar Apq B≤A b = goal
  where
  private hh = ∣ B≤A ∣ ; h = _⟨$⟩_ ∣ hh ∣
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ )
  open Setoid 𝔻[ 𝑩 ]  using () renaming ( _≈_ to _≈ᴮ_ )
  open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
  open Environment 𝑩  using ( ⟦_⟧ )
  open SetoidReasoning 𝔻[ 𝑨 ]

  ξ : ∀ b → h (⟦ p ⟧ ⟨$⟩ b) ≈ h (⟦ q ⟧ ⟨$⟩ b)
  ξ b = begin
         h (⟦ p ⟧  ⟨$⟩         b)  ≈⟨   comm-hom-term hh p b  ⟩
         ⟦ p ⟧ᴬ    ⟨$⟩  (h  ∘  b)  ≈⟨   Apq (h ∘ b)           ⟩
         ⟦ q ⟧ᴬ    ⟨$⟩  (h  ∘  b)  ≈˘⟨  comm-hom-term hh q b  ⟩
         h (⟦ q ⟧  ⟨$⟩         b)  ∎

  goal : ⟦ p ⟧ ⟨$⟩ b ≈ᴮ ⟦ q ⟧ ⟨$⟩ b
  goal = ∥ B≤A ∥ (ξ b)
\end{code}

\paragraph*{Product invariance of ⊧}
An identity satisfied by all algebras in an indexed collection is also satisfied by the product of algebras in that collection.

\begin{code}

module _ {X : Type χ}{I : Type ℓ}(𝒜 : I → Algebra α ρᵃ){p q : Term X} where

 ⊧-P-invar : (∀ i → 𝒜 i ⊧ (p ≈̇ q)) → ⨅ 𝒜 ⊧ (p ≈̇ q)
 ⊧-P-invar 𝒜pq a =
  begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨   ξ                  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a  ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎
  where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]
  ξ : ( λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (a x) i ) ≈ ( λ i → (⟦ 𝒜 i ⟧ q) ⟨$⟩ λ x → (a x) i )
  ξ = λ i → 𝒜pq i (λ x → (a x) i)
\end{code}


\paragraph*{PS ⊆ SP}
Another important fact we will need about the operators \af S and \af P is that a product of subalgebras of algebras in a class \ab{𝒦} is a subalgebra of a product of algebras in \ab{𝒦}. We denote this inclusion by \af{PS⊆SP}, which we state and prove as follows.

\begin{code}

module _  {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private
  a = α ⊔ ρᵃ
  oaℓ = ov (a ⊔ ℓ)

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

\paragraph*{Identity preservation}
The classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦}, and \af V \ab{𝒦} all satisfy the same set of equations.  We will only use a subset of the inclusions used to prove this fact. (For a complete proof, see the
\ualmodule{Varieties.Func.Preservation} module of the \agdaalgebras library.)


\paragraph*{H preserves identities}
First we prove that the closure operator \af H is compatible with identities that hold in the given class.

\begin{code}

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where

 H-id1 : 𝒦 ⊫ (p ≈̇ q) → (H {β = α}{ρᵃ}ℓ 𝒦) ⊫ (p ≈̇ q)
 H-id1 σ 𝑩 (𝑨 , kA , BimgOfA) ρ =
  begin
   ⟦ p ⟧       ⟨$⟩                 ρ     ≈˘⟨  cong ⟦ p ⟧ ζ                  ⟩
   ⟦ p ⟧       ⟨$⟩  (φ  ∘  φ⁻¹  ∘  ρ)    ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)  ⟩
   φ ( ⟦ p ⟧ᴬ  ⟨$⟩  (      φ⁻¹  ∘  ρ) )  ≈⟨   cong ∣ φh ∣ (IH (φ⁻¹ ∘ ρ))    ⟩
   φ ( ⟦ q ⟧ᴬ  ⟨$⟩  (      φ⁻¹  ∘  ρ) )  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)  ⟩
   ⟦ q ⟧       ⟨$⟩  (φ  ∘  φ⁻¹  ∘  ρ)    ≈⟨   cong ⟦ q ⟧ ζ                  ⟩
   ⟦ q ⟧       ⟨$⟩                 ρ     ∎
    where
    open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
    open Environment 𝑩  using ( ⟦_⟧ )
    open Setoid 𝔻[ 𝑩 ]  using ( _≈_ )
    open SetoidReasoning 𝔻[ 𝑩 ]

    IH : 𝑨 ⊧ (p ≈̇ q)
    IH = σ 𝑨 kA

    φh : hom 𝑨 𝑩
    φh = ∣ BimgOfA ∣
    private φ = (_⟨$⟩_ ∣ φh ∣)

    φE : IsSurjective ∣ φh ∣
    φE = ∥ BimgOfA ∥

    φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
    φ⁻¹ = SurjInv ∣ φh ∣ φE

    ζ : ∀ x → (φ ∘ φ⁻¹ ∘ ρ) x ≈ ρ x
    ζ = λ _ → InvIsInverseʳ φE


\end{code}

\paragraph*{S preserves identities}

\begin{code}

 S-id1 : 𝒦 ⊫ (p ≈̇ q) → (S {β = α}{ρᵃ} ℓ 𝒦) ⊫ (p ≈̇ q)
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

\end{code}

The obvious converse is barely worth the bits needed to formalize it, but we will use it below, so let's prove it now.

\begin{code}

 S-id2 : S ℓ 𝒦 ⊫ (p ≈̇ q) → 𝒦 ⊫ (p ≈̇ q)
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))
\end{code}


\paragraph*{P preserves identities}

\begin{code}

 P-id1 : ∀{ι} → 𝒦 ⊫ (p ≈̇ q) → P {β = α}{ρᵃ}ℓ ι 𝒦 ⊫ (p ≈̇ q)
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A)
  where
  ih : ∀ i → 𝒜 i ⊧ (p ≈̇ q)
  ih i = σ (𝒜 i) (kA i)
  IH : ⨅ 𝒜 ⊧ (p ≈̇ q)
  IH = ⊧-P-invar 𝒜 {p}{q} ih
\end{code}


\paragraph*{V preserves identities}
Finally, we prove the analogous preservation lemmas for the closure operator \af V.

\begin{code}

module _ {X : Type χ}{ι : Level}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private
  aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι

 V-id1 : 𝒦 ⊫ (p ≈̇ q) → V ℓ ι 𝒦 ⊫ (p ≈̇ q)
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA))
   where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ (p ≈̇ q)
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
\end{code}

\paragraph*{Th 𝒦 ⊆ Th (V 𝒦)}
From \af{V-id1} it follows that if \ab{𝒦} is a class of algebras, then the set of identities modeled by the algebras in \ab{𝒦} is contained in the set of identities modeled by the algebras in \af V \ab{𝒦}.  In other terms, \af{Th} \ab{𝒦} \aof{⊆} \af{Th} (\af V \ab{𝒦}).  We formalize this observation as follows.

\begin{code}

 classIds-⊆-VIds : 𝒦 ⊫ (p ≈̇ q)  → (p , q) ∈ Th (V ℓ ι 𝒦)
 classIds-⊆-VIds pKq 𝑨 = V-id1 pKq 𝑨
\end{code}




%% -------------------------------------------------------------------------------------

\section{Free Algebras and the HSP Theorem}
\label{free-algebras-and-the-hsp-theorem}

\subsection{The absolutely free algebra 𝑻 X}
\label{the-absolutely-free-algebra-tx}

The term algebra \af{𝑻} \ab X is \emph{absolutely free} (or \emph{universal}, or
\emph{initial}) for algebras in the signature \ab{𝑆}. That is, for every
\ab{𝑆}-algebra \ab{𝑨}, the following hold.

\begin{itemize}
\item Every function from \ab{𝑋} to \aof{∣} \ab{𝑨} \aof{∣} lifts to a
  homomorphism from \af{𝑻} \ab{X} to \ab{𝑨}.
\item The homomorphism that exists by item 1 is unique.
\end{itemize}

We now prove this in \agda, starting with the fact that every map from \ab{X} to
\aof{∣} \ab{𝑨} \aof{∣} lifts to a map from \aof{∣} \af{𝑻} \ab{X} \aof{∣} to
\aof{∣} \ab{𝑨} \aof{∣} in a natural way, by induction on the structure of the given term.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 open Setoid 𝔻[ 𝑨 ] using ( _≈_ ; reflexive ; refl ; trans )

 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x) = h x
 free-lift (node f t) = (f ̂ 𝑨) (λ i → free-lift (t i))

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong
  where
  flcong : ∀ {s t} → s ≐ t →  free-lift s ≈ free-lift t
  flcong (_≐_.rfl x) = reflexive (≡.cong h x)
  flcong (_≐_.gnl x) = cong (Interp 𝑨) (≡.refl , (λ i → flcong (x i)))

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
  hcomp {f}{a} = cong (Interp 𝑨) (≡.refl , (λ i → (cong free-lift-func){a i} ≐-isRefl))

  hhom : IsHom (𝑻 X) 𝑨 hfunc
  hhom = mkhom (λ{f}{a} → hcomp{f}{a})


module _ {X : Type χ}{𝑨 : Algebra α ρᵃ} where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift {𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x) = refl
 free-lift-interp η (node f t) = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}




\subsection{The relatively free algebra 𝔽[ X ]}
\label{the-relatively-free-algebra-f}

We now define the algebra
\AgdaOperator{\AgdaFunction{𝔽[}}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]}},
which represents the relatively free algebra.
Here, as above, \ab X plays the role of an arbitrary nonempty collection of variables. (It would suffice to take\ab X to be the cardinality of the largest algebra in \ab{𝒦}, but since we don't know that cardinality, we leave \ab X aribtrary for now.)

\begin{code}

module FreeAlgebra {χ : Level}{ι : Level}{I : Type ι}(ℰ : I → Eq) where
 open Algebra

 FreeDomain : Type χ → Setoid _ _
 FreeDomain X = record  { Carrier        = Term X
                        ; _≈_            = ℰ ⊢ X ▹_≈_
                        ; isEquivalence  = ⊢▹≈IsEquiv }
\end{code}

The interpretation of an operation is simply the operation itself.
This works since
\AgdaBound{ℰ}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{⊢}}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{▹\AgdaUnderscore{}≈\AgdaUnderscore{}}}
is a congruence.

\begin{code}

 FreeInterp : ∀ {X} → ⟨ 𝑆 ⟩ (FreeDomain X) ⟶ FreeDomain X
 FreeInterp ⟨$⟩ (f , ts) = node f ts
 cong FreeInterp (≡.refl , h) = app h

 𝔽[_] : Type χ → Algebra (ov χ) (ι ⊔ ov χ)
 Domain 𝔽[ X ] = FreeDomain X
 Interp 𝔽[ X ] = FreeInterp
\end{code}

\subsection{Basic properties of free algebras}
\label{basic-properties-of-free-algebras}

\begin{code}

module FreeHom (χ : Level) {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(χ ⊔ α ⊔ ρᵃ ⊔ ℓ)
 open Eq

 ℐ : Type ι -- indexes the collection of equations modeled by 𝒦
 ℐ = Σ[ eq ∈ Eq{χ} ] 𝒦 ⊫ ((lhs eq) ≈̇ (rhs eq))

 ℰ : ℐ → Eq
 ℰ (eqv , p) = eqv

 ℰ⊢[_]▹Th𝒦 : (X : Type χ) → ∀{p q} → ℰ ⊢ X ▹ p ≈ q → 𝒦 ⊫ (p ≈̇ q)
 ℰ⊢[ X ]▹Th𝒦 x 𝑨 kA = sound (λ i ρ → ∥ i ∥ 𝑨 kA ρ) x where open Soundness ℰ 𝑨
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )
\end{code}


\paragraph*{The natural epimorphism from 𝑻 X to 𝔽[ X ]}
We now define the natural epimorphism from
\T{X} onto the relatively free algebra \Free{X} and prove that 
the kernel of this morphism is the congruence of \T{X}
defined by the identities modeled by (\af S \ab{𝒦}, hence by) \ab{𝒦}.

\begin{code}

 epi𝔽[_] : (X : Type χ) → epi (𝑻 X) 𝔽[ X ]
 epi𝔽[ X ] = h , hepi
  where
  open Algebra (𝑻 X)   using () renaming ( Domain  to TX    )
  open Algebra 𝔽[ X ]  using () renaming ( Domain  to F     )
  open Setoid TX       using () renaming ( _≈_     to _≈₀_  ; refl to refl₀ )
  open Setoid F        using () renaming ( _≈_     to _≈₁_  ; refl to refl₁ )
  open _≐_

  c : ∀ {x y} → x ≈₀ y → x ≈₁ y
  c (rfl {x}{y} ≡.refl) = refl₁
  c (gnl {f}{s}{t} x) = cong (Interp 𝔽[ X ]) (≡.refl , c ∘ x)

  h : TX ⟶ F
  h = record { f = id ; cong = c }

  hepi : IsEpi (𝑻 X) 𝔽[ X ] h
  compatible (isHom hepi) = cong h refl₀
  isSurjective hepi {y} = eq y refl₁

 hom𝔽[_] : (X : Type χ) → hom (𝑻 X) 𝔽[ X ]
 hom𝔽[ X ] = IsEpi.HomReduct ∥ epi𝔽[ X ] ∥

 hom𝔽[_]-is-epic : (X : Type χ) → IsSurjective ∣ hom𝔽[ X ] ∣
 hom𝔽[ X ]-is-epic = IsEpi.isSurjective (snd (epi𝔽[ X ]))
\end{code}

As promised, we prove that the kernel of the natural epimorphism is the congruence defined by the identities modelled by \ab{𝒦}.

\begin{code}

 class-models-kernel : ∀{X p q} → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣ → 𝒦 ⊫ (p ≈̇ q)
 class-models-kernel {X = X}{p}{q} pKq = ℰ⊢[ X ]▹Th𝒦 pKq

 kernel-in-theory : {X : Type χ} → ker ∣ hom𝔽[ X ] ∣ ⊆ Th (V ℓ ι 𝒦)
 kernel-in-theory {X = X} {p , q} pKq vkA x = classIds-⊆-VIds {ℓ = ℓ}{p = p}{q}
                                               (class-models-kernel pKq) vkA x

 module _ {X : Type χ} {𝑨 : Algebra α ρᵃ}{sA : 𝑨 ∈ S {β = α}{ρᵃ} ℓ 𝒦} where
  open Environment 𝑨 using ( Equal )
  ker𝔽⊆Equal : ∀{p q} → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣ → Equal p q
  ker𝔽⊆Equal{p = p}{q} x = S-id1{ℓ = ℓ}{p = p}{q} (ℰ⊢[ X ]▹Th𝒦 x) 𝑨 sA

 𝒦⊫→ℰ⊢ : {X : Type χ} → ∀{p q} → 𝒦 ⊫ (p ≈̇ q) → ℰ ⊢ X ▹ p ≈ q
 𝒦⊫→ℰ⊢ {p = p} {q} pKq = hyp ((p ≈̇ q) , pKq) where open _⊢_▹_≈_ using (hyp)
\end{code}

\paragraph*{The universal property}

\begin{code}

module _  {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ) (α ⊔ ρᵃ ⊔ ℓ)} {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)

 open FreeHom {ℓ = ℓ}(α ⊔ ρᵃ ⊔ ℓ) {𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ  using ( 𝔽[_] )
 open Setoid 𝔻[ 𝑨 ]                 using ( trans ; sym ; refl ) renaming ( Carrier to A )


 𝔽-ModTh-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦))
  →            epi 𝔽[ A ] 𝑨
 𝔽-ModTh-epi A∈ModThK = φ , isEpi
  where
   φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
   _⟨$⟩_ φ = free-lift{𝑨 = 𝑨} id
   cong φ {p} {q} pq  = trans  ( sym (free-lift-interp{𝑨 = 𝑨} id p) )
                      ( trans  ( A∈ModThK{p = p}{q} (kernel-in-theory pq) id )
                               ( free-lift-interp{𝑨 = 𝑨} id q ) )
   isEpi : IsEpi 𝔽[ A ] 𝑨 φ
   compatible (isHom isEpi) = cong (Interp 𝑨) (≡.refl , (λ _ → refl))
   isSurjective isEpi {y} = eq (ℊ y) refl

 𝔽-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 𝔽-ModTh-epi-lift A∈ModThK = ∘-epi (𝔽-ModTh-epi (λ {p q} → A∈ModThK{p = p}{q})) ToLift-epi
\end{code}



%% -------------------------------------------------------------------------------------

\subsection{Products of classes of algebras}
\label{products-of-classes-of-algebras}

We want to pair each (\ab{𝑨} , \ab p) (where \ab p : \ab{𝑨} \af{∈} \af S \ab{𝒦}) with an environment
\ab{ρ} : \ab X \as{→} \aof{∣} \ab{𝑨} \aof{∣} so that we can quantify over all algebras \emph{and} all
assignments of values in the domain \aof{∣} \ab{𝑨} \aof{∣} to variables in \ab X.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)
 open FreeHom {ℓ = ℓ} (α ⊔ ρᵃ ⊔ ℓ){𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ  using ( 𝔽[_] )
 open Environment                   using ( Env )

 ℑ⁺ : Type ι
 ℑ⁺ = Σ[ 𝑨 ∈ (Algebra α ρᵃ) ] (𝑨 ∈ S ℓ 𝒦) × (Carrier (Env 𝑨 X))

 𝔄⁺ : ℑ⁺ → Algebra α ρᵃ
 𝔄⁺ i = ∣ i ∣

 ℭ : Algebra ι ι
 ℭ = ⨅ 𝔄⁺

\end{code}

Next we define a useful type, \af{skEqual}, which we use to represent a term identity \ab p \aic{≈} \ab q for any
given \ab i = (\ab{𝑨} , \ab{sA} , \ab{ρ}) (where \ab{𝑨} is an algebra, \ab{sA} : \ab{𝑨} \af{∈} \af{S} \ab{𝒦} is a proof that \ab{𝑨} belongs to \af{S} \ab{𝒦}, and \ab{ρ} is a mapping from \ab X to the domain of \ab{𝑨}). Then we prove \af{AllEqual⊆ker𝔽} which asserts that if the identity \ab{p} \aic{≈} \ab q holds in all \ab{𝑨} \aof{∈} \af S \ab{𝒦} (for all environments), then \ab p \aic{≈} \ab q
holds in the relatively free algebra
\Free{X}; equivalently, the pair (\ab p , \ab q) belongs to the
kernel of the natural homomorphism from
\T{X} onto \Free{X}. We will use this fact below to prove
that there is a monomorphism from \Free{X} into \ab{ℭ}, and thus \Free{X} is a subalgebra of \ab{ℭ},
so belongs to \af S (\af P \ab{𝒦}).

\begin{code}

 skEqual : (i : ℑ⁺) → ∀{p q} → Type ρᵃ
 skEqual i {p}{q} = ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
  where
  open Setoid 𝔻[ 𝔄⁺ i ]    using ( _≈_ )
  open Environment (𝔄⁺ i)  using ( ⟦_⟧ )

 AllEqual⊆ker𝔽 : ∀ {p q} → (∀ i → skEqual i {p}{q}) → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣
 AllEqual⊆ker𝔽 {p} {q} x = Goal
  where
  open Setoid 𝔻[ 𝔽[ X ] ] using ( _≈_ )
  S𝒦⊫pq : S{β = α}{ρᵃ} ℓ 𝒦 ⊫ (p ≈̇ q)
  S𝒦⊫pq 𝑨 sA ρ = x (𝑨 , sA , ρ)
  Goal : p ≈ q
  Goal = 𝒦⊫→ℰ⊢ (S-id2{ℓ = ℓ}{p = p}{q} S𝒦⊫pq)

 homℭ : hom (𝑻 X) ℭ
 homℭ = ⨅-hom-co 𝔄⁺ h
  where
  h : ∀ i → hom (𝑻 X) (𝔄⁺ i)
  h i = lift-hom (snd ∥ i ∥)

 ker𝔽⊆kerℭ : ker ∣ hom𝔽[ X ] ∣ ⊆ ker ∣ homℭ ∣
 ker𝔽⊆kerℭ {p , q} pKq (𝑨 , sA , ρ) = Goal
  where
  open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; sym ; trans )
  open Environment 𝑨  using ( ⟦_⟧ )
  fl : ∀ t → ⟦ t ⟧ ⟨$⟩ ρ ≈ free-lift ρ t
  fl t = free-lift-interp {𝑨 = 𝑨} ρ t
  subgoal : ⟦ p ⟧ ⟨$⟩ ρ ≈ ⟦ q ⟧ ⟨$⟩ ρ
  subgoal = ker𝔽⊆Equal{𝑨 = 𝑨}{sA} pKq ρ
  Goal : (free-lift{𝑨 = 𝑨} ρ p) ≈ (free-lift{𝑨 = 𝑨} ρ q)
  Goal = trans (sym (fl p)) (trans subgoal (fl q))


 hom𝔽ℭ : hom 𝔽[ X ] ℭ
 hom𝔽ℭ = ∣ HomFactor ℭ homℭ hom𝔽[ X ] ker𝔽⊆kerℭ hom𝔽[ X ]-is-epic ∣

 kerℭ⊆ker𝔽 : ∀{p q} → (p , q) ∈ ker ∣ homℭ ∣ → (p , q) ∈ ker ∣ hom𝔽[ X ] ∣
 kerℭ⊆ker𝔽 {p}{q} pKq = E⊢pq
  where
  pqEqual : ∀ i → skEqual i {p}{q}
  pqEqual i = goal
   where
   open Environment (𝔄⁺ i)  using ( ⟦_⟧ )
   open Setoid 𝔻[ 𝔄⁺ i ]    using ( _≈_ ; sym ; trans )
   goal : ⟦ p ⟧ ⟨$⟩ snd ∥ i ∥ ≈ ⟦ q ⟧ ⟨$⟩ snd ∥ i ∥
   goal = trans (free-lift-interp{𝑨 = ∣ i ∣}(snd ∥ i ∥) p)
           (trans (pKq i)(sym (free-lift-interp{𝑨 = ∣ i ∣} (snd ∥ i ∥) q)))
  E⊢pq : ℰ ⊢ X ▹ p ≈ q
  E⊢pq = AllEqual⊆ker𝔽 pqEqual

 mon𝔽ℭ : mon 𝔽[ X ] ℭ
 mon𝔽ℭ = ∣ hom𝔽ℭ ∣ , isMon
  where
  isMon : IsMon 𝔽[ X ] ℭ ∣ hom𝔽ℭ ∣
  isHom isMon = ∥ hom𝔽ℭ ∥
  isInjective isMon {p} {q} φpq = kerℭ⊆ker𝔽 φpq

\end{code}

Now that we have proved the existence of a monomorphism from \Free{X} to \ab{ℭ} we can
prove that \Free{X} is a subalgebra of \ab{ℭ}, so belongs to \af S (\af P \ab{𝒦}).

\begin{code}

 𝔽≤ℭ : 𝔽[ X ] ≤ ℭ
 𝔽≤ℭ = mon→≤ mon𝔽ℭ

 SP𝔽 : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SP𝔽 = S-idem SSP𝔽
  where
  PSℭ : ℭ ∈ P (α ⊔ ρᵃ ⊔ ℓ) ι (S ℓ 𝒦)
  PSℭ = ℑ⁺ , (𝔄⁺ , ((λ i → fst ∥ i ∥) , ≅-refl))
  SPℭ : ℭ ∈ S ι (P ℓ ι 𝒦)
  SPℭ = PS⊆SP {ℓ = ℓ} PSℭ
  SSP𝔽 : 𝔽[ X ] ∈ S ι (S ι (P ℓ ι 𝒦))
  SSP𝔽 = ℭ , (SPℭ , 𝔽≤ℭ)
\end{code}



%% -------------------------------------------------------------------------------------

\subsection{The HSP Theorem}

Finally, we are in a position to prove Birkhoff's celebrated variety theorem.

\begin{code}

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private ι = ov(α ⊔ ρᵃ ⊔ ℓ)
 open FreeHom {ℓ = ℓ}(α ⊔ ρᵃ ⊔ ℓ){𝒦}
 open FreeAlgebra {ι = ι}{I = ℐ} ℰ using ( 𝔽[_] )

 Birkhoff : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Birkhoff 𝑨 ModThA = V-≅-lc{α}{ρᵃ}{ℓ} 𝒦 𝑨 VlA
  where
  open Setoid 𝔻[ 𝑨 ] using () renaming ( Carrier to A )
  sp𝔽A : 𝔽[ A ] ∈ S{ι} ι (P ℓ ι 𝒦)
  sp𝔽A = SP𝔽{ℓ = ℓ} 𝒦
  epi𝔽lA : epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
  epi𝔽lA = 𝔽-ModTh-epi-lift{ℓ = ℓ} (λ {p q} → ModThA{p = p}{q})
  lAimg𝔽A : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ A ]
  lAimg𝔽A = epi→ontohom 𝔽[ A ] (Lift-Alg 𝑨 ι ι) epi𝔽lA
  VlA : Lift-Alg 𝑨 ι ι ∈ V ℓ ι 𝒦
  VlA = 𝔽[ A ] , sp𝔽A , lAimg𝔽A

\end{code}

The converse inclusion, \af V \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} (\af V \ab{𝒦})), is a simple consequence of the fact that \af{Mod} \af{Th} is a closure operator. Nonetheless, completeness demands
that we formalize this inclusion as well, however trivial the proof.

\begin{code}

 module _ {𝑨 : Algebra α ρᵃ} where
  Birkhoff-converse : 𝑨 ∈ V{α}{ρᵃ}{α}{ρᵃ}{α}{ρᵃ} ℓ ι 𝒦 → 𝑨 ∈ Mod{X = 𝕌[ 𝑨 ]} (Th (V ℓ ι 𝒦))
  Birkhoff-converse vA pThq = pThq 𝑨 vA

\end{code}

We have thus proved that every variety is an equational class.

Readers familiar with the classical formulation of the Birkhoff HSP theorem as an
``if and only if'' assertion might worry that the proof is still incomplete. However,
recall that in the \ualmodule{Varieties.Func.Preservation} module we proved the following
identity preservation lemma:\\[4pt]
\ab{V-id1} : \ab{𝒦} \aof{⊫} \ab p \aic{≈̇} \ab q \as{→} \af{V} \ab{𝒦} \aof{⊫} \ab p \aic{≈̇} \ab q
\\[4pt]
Thus, if \ab{𝒦} is an equational class---that is, if \ab{𝒦} is the class of algebras
satisfying all identities in some set---then \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.  On the other hand, we
proved that \af V is expansive in the \ualmodule{Varieties.Func.Closure} module:

\ab{V-expa} : \ab{𝒦} \aof{⊆} \af V \ab{𝒦}

so \ab{𝒦} (= \af V \ab{𝒦} = \af H \af S \af P \ab{𝒦}) is a variety.

Taken together, \af{V-id1} and \af{V-expa} constitute formal proof that every equational
class is a variety. This completes the formal proof of Birkhoff's variety theorem.


