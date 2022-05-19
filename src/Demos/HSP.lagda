% Workflow for TYPES 2021 paper:
% 1. Edit/improve the literate Agda file `src/Demos/HSP.lagda`.
% 2. Invoke `agda --latex --latex-dir=doc/TYPES2021 src/Demos/HSP.lagda` from the main `agda-algebras` directory.
% 3. Invoke `pdflatex agda-hsp` from within the `doc/TYPES2021` directory.

\section{Introduction}
The Agda Universal Algebra Library (\agdaalgebras) \cite{ualib_v2.0.1} formalizes the foundations of universal algebra
in intensional Martin-Löf type theory (\mltt) using \agda~\cite{Norell:2007,agdaref}.
The library includes a collection of definitions and verified theorems originated in classical
(set-theory based) universal algebra and equational logic, but adapted to \mltt.

The first major milestone of the project is a complete formalization of \emph{Birkhoff's
variety theorem} (also known as the \emph{HSP theorem})~\cite{Birkhoff:1935}.
To the best of our knowledge, this is the first time Birkhoff's celebrated 1935 result
has been formalized in \mltt.\footnote{An alternative formalization based on classical
set-theory was achieved in~\cite{birkhoff-in-mizar:1999}.}
%; see \href{http://www.mizar.org/JFM/Vol9/birkhoff.html\#BIB21}{mizar.org/JFM/Vol9/birkhoff.html}.}

Our first attempt to formalize Birkhoff's theorem
suffered from two flaws.\footnote{See the
 \href{https://github.com/ualib/ualib.github.io/blob/71f173858701398d56224dd79d152c380c0c2b5e/src/lagda/UALib/Birkhoff.lagda}{\textsf{Birkhoff.lagda}} file
 in the \href{https://github.com/ualib/ualib.github.io}{\textsf{ualib/ualib.gitlab.io}}
 repository (\href{https://github.com/ualib/ualib.github.io/commit/71f173858701398d56224dd79d152c380c0c2b5e}{15
 Jan 2021 commit 71f1738})~\cite{ualib_v1.0.0}.}
First, we assumed function extensionality in \mltt; consequently, it was unclear whether the formalization was fully constructive.  Second, an inconsistency could be
contrived by taking the type \ab{X}, representing an arbitrary collection of
variable symbols, to be the two element type (see §\ref{sec:discuss} for details).  To resolve these issues, we developed a new formalization of the HSP theorem based on \textit{setoids} and rewrote much of the \agdaalgebras library to support this approach.  This enabled us to avoid function extensionality altogether.  Moreover, the type \ab{X} of variable symbols was treated with more care using the \textit{context} and \textit{environment} types that Andreas Abel uses in~\cite{Abel:2021} to formalize Birkhoff's completeness theorem. These design choices are discussed further in §\ref{setoids}--\ref{setoid-functions}.

What follows is a self-contained formal proof of the HSP theorem in \agda.
%\footnote{The proof presented here is based on \agdaalgebras, ver.~2.0.1~\cite{ualib_v2.0.1}, \agda ver.2.6.2 a%nd \agdastdlib ver.1.7.}
%is constructive and correct.
This is achieved by
extracting a subset of the \agdaalgebras library, including only the
pieces needed for the proof, into a single literate \agda file.\footnote{%
\HSPlagda in the \agdaalgebras repository: \agdaalgebrasrepo}
\ifshort %%% BEGIN SHORT VERSION ONLY
For spaces reasons, we elide some inessential parts,
but strive to preserve the essential content and character of the development.
Specifically, routine or overly technical components, as well as anything that does not
seem to offer insight into the central ideas of the proof are omitted. (The file \HSPlagda mentioned above includes the full proof.)
%can be found in the file \HSPlagda in the \agdaalgebras repository.}
%or in the unabridged version of the present paper~\cite{DeMeo:2021}.}
       %%% END SHORT VERSION ONLY
\else  %%% BEGIN LONG VERSION ONLY
We include here every line of code of our new proof of Birkhoff's theorem
in a single \agda module, presented as a literate \agda document,\footnote{See
\HSPlagda in the \agdaalgebras repository: \agdaalgebrasrepo .}.  Apart from a few dozen
imports from the \agdastdlib, the module is self-contained.
\fi

In this paper, we highlight some of the more challenging aspects of formalizing universal algebra in type theory.  To some extent, this is a sobering glimpse of the significant technical hurdles that must be overcome to do mathematics in dependent type theory. Nonetheless, we hope to demonstrate that \mltt is a relatively natural language for formalizing universal algebra.  Indeed, we believe that researchers with sufficient patience and resolve can reap the substantial rewards of deeper insight and greater confidence in their results by using type theory and a proof assistant like \agda.
On the other hand, this paper is probably not the best place to learn about the latter, since we assume the reader is already familiar with \mltt and \agda.
In summary, our main contribution is to show that a straightforward but very general representation of algebraic structures in dependent type theory is quite practical, as we demonstrate by formalizing a major seminal result of universal algebra.

\section{Preliminaries}

\subsection{Logical foundations}

To best emulate \mltt, we use
\begin{code}[inline]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
;
\ifshort  %%% BEGIN SHORT VERSION ONLY
  \AgdaPragma{without-K} disables
  \href{https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29}{Streicher's K axiom};
  \AgdaPragma{exact-split} directs \agda to accept only definitions behaving like
  {\it judgmental} equalities;
  \AgdaPragma{safe} ensures that nothing is postulated outright.
  (See~\cite{agdaref-axiomk,agdaref-safeagda,agdatools-patternmatching}.)
       %%% END SHORT VERSION ONLY
\else  %%% BEGIN LONG VERSION ONLY

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
\fi    %%% END LONG VERSION ONLY
We also make use of the following definitions from \agda's standard library (ver.~1.7).
\begin{code}[hide]
{-# OPTIONS --without-K --exact-split --safe #-}
\end{code}
\ifshort
\else  %%% BEGIN LONG VERSION ONLY
\begin{code}
-- Import universe levels and Signature type (described below) from the agda-algebras library.
open import Base.Algebras.Basic using ( 𝓞 ; 𝓥 ; Signature )
module Demos.HSP {𝑆 : Signature 𝓞 𝓥} where
\end{code}
\fi    %%% END LONG VERSION ONLY
{\small
\begin{code}

-- Import 16 definitions from the Agda Standard Library.
open import  Data.Unit.Polymorphic        using ( ⊤ ; tt                                            )
open import  Function                     using ( id ; _∘_ ; flip                                   )
open import  Level                        using ( Level                                             )
open import  Relation.Binary              using ( Rel ; Setoid ; IsEquivalence                      )
open import  Relation.Binary.Definitions  using ( Reflexive ; Symmetric ; Transitive ; Sym ; Trans  )
open import  Relation.Binary.PropositionalEquality  using ( _≡_                                     )
open import  Relation.Unary               using ( Pred ; _⊆_ ; _∈_                                  )

-- -- Import 23 definitions from the Agda Standard Library and rename 12 of them.
open import  Agda.Primitive  renaming  ( Set    to Type    )  using  ( _⊔_ ; lsuc                   )
open import  Data.Product    renaming  ( proj₁  to fst     )  using  ( _×_ ; _,_ ; Σ ; Σ-syntax     )
                             renaming  ( proj₂  to snd     )
open import  Function        renaming  ( Func   to _⟶_     )  using  (                              )
open         _⟶_             renaming  ( f      to _⟨$⟩_   )  using  ( cong                         )
open         IsEquivalence   renaming  ( refl   to reflᵉ   )
                             renaming  ( sym    to symᵉ    )
                             renaming  ( trans  to transᵉ  )  using  (                              )
open         Setoid          renaming  ( refl   to reflˢ   )
                             renaming  ( sym    to symˢ    )
                             renaming  ( trans  to transˢ  )
                             renaming  ( _≈_ to _≈ˢ_       )  using  ( Carrier  ; isEquivalence     )

-- Assign handles to 3 modules of the Agda Standard Library.
import       Function.Definitions                   as   FD
import       Relation.Binary.PropositionalEquality  as   ≡
import       Relation.Binary.Reasoning.Setoid       as   SetoidReasoning

private variable α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ ρ χ ℓ : Level ;       Γ Δ : Type χ

\end{code}
}
\noindent The above imports include some adjustments to ``standard'' \agda syntax; in particular,
we use \AgdaPrimitive{Type} in place of \AgdaPrimitive{Set}, the infix long arrow symbol,
\AgdaRecord{\AgdaUnderscore{}⟶\AgdaUnderscore{}}, in place of \AgdaRecord{Func} (the type of ``setoid functions,'' discussed in §\ref{setoid-functions} below), and the symbol \aofld{\au{}⟨\$⟩\au{}} in place of \afld{f} (application of the map of a setoid function); we use
\AgdaField{fst} and \AgdaField{snd}, and sometimes \AgdaOperator{\AgdaFunction{∣\AgdaUnderscore{}∣}} and
\AgdaOperator{\AgdaFunction{∥\AgdaUnderscore{}∥}}, to denote the first and second
projections out of the product type
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}×\AgdaUnderscore{}}}.
\ifshort
\else  %%% BEGIN LONG VERSION ONLY

\begin{code}
module _ {A : Type α }{B : A → Type β} where
 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣_∣ = fst
 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥_∥ = snd
\end{code}
\fi       %%% END LONG VERSION ONLY


%% -----------------------------------------------------------------------------
\subsection{Setoids}\label{setoids}
A \defn{setoid} is a pair consisting of a type and
an equivalence relation on that type.  Setoids are useful for representing a
set with an explicit, ``local'' notion of equivalence, instead of relying on
an implicit, ``global'' one as is more common in set theory. In reality,
informal mathematical practice relies on equivalence relations quite pervasively,
taking great care to define only functions that preserve equivalences, while eliding the
details. To be properly formal, such details must be made explicit.
While there are many different workable approaches, the one that requires
no additional meta-theory is based on setoids, which is why we adopt it here.
While in some settings setoids are found by others to be burdensome, we have not
found them to be so for universal algebra.

The \agdaalgebras library was first developed without setoids, relying on
propositional equality %\ad{\au{}≡\au{}}
instead,
along with some experimental, domain-specific types for equivalence classes, quotients, etc.
This required postulating function extensionality,%
\footnote{the axiom asserting that two point-wise equal functions are equal} which is
known to be independent from \mltt~\cite{MHE, MHE:2019}; this was unsatisfactory as %we were curious to see if
we aimed to show that the theorems hold directly in \mltt without extra axioms.
The present work makes no appeal to functional extensionality or classical axioms like Choice or Excluded Middle.\footnote{All submodules of the \am{Setoid} module in the \agdaalgebras library are also fully constructive in this sense.}


%% -----------------------------------------------------------------------------
\subsection{Setoid functions}
\label{setoid-functions}
A \textit{setoid function} is a function from
one setoid to another that respects the underlying equivalences.
If \ab{𝑨} and \ab{𝑩} are setoids, we use \ab{𝑨}~\AgdaRecord{⟶}~\ab{𝑩}
to denote the type of setoid functions from \ab{𝑨} to \ab{𝑩}.
\ifshort
\else %%% BEGIN LONG VERSION ONLY

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
\paragraph*{Inverses}
\fi %%% END LONG VERSION ONLY
We define the \defn{inverse} of such a function in terms of the image of the function's domain, as follows.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where
 open Setoid 𝑩 using ( _≈_ ; sym ) renaming ( Carrier to B )

 data Image_∋_ (f : 𝑨 ⟶ 𝑩) : B → Type (α ⊔ β ⊔ ρᵇ) where
  eq : {b : B} → ∀ a → b ≈ f ⟨$⟩ a → Image f ∋ b

\end{code}

An inhabitant of the \aod{Image} \ab f \aod{∋} \ab b type is a point \ab a~\as :~\afld{Carrier}\ab{𝑨},
along with a proof \ab p~\as :~\ab b~\af{≈}~\ab f~\ab a, that \ab f maps \ab a to \ab b.
Since a proof of \aod{Image} \ab f \aod{∋} \ab b must include a concrete witness \ab a~\as :~\afld{Carrier}~\ab{𝑨}, we can actually \emph{compute} a range-restricted right-inverse of \ab f.
Here is the definition of \af{Inv} which, for extra certainty, is accompanied by a proof that it gives a right-inverse.

\begin{code}

 Inv : (f : 𝑨 ⟶ 𝑩){b : B} → Image f ∋ b → Carrier 𝑨
 Inv _ (eq a _) = a

 InvIsInverseʳ : {f : 𝑨 ⟶ 𝑩}{b : B}(q : Image f ∋ b) → f ⟨$⟩ (Inv f q) ≈ b
 InvIsInverseʳ (eq _ p) = sym p
\end{code}
%
\ifshort\else
\paragraph*{Injective and surjective setoid functions}
\fi

If \ab{f} : \ab{𝑨} \aor{⟶} \ab{𝑩}
then we call \ab f \defn{injective} provided
\as{∀}(\ab{a₀} \ab{a₁} \as : \ab{A}), \ab{f}~\aofld{⟨\$⟩}~\ab{a₀}~\af{≈ᴮ}~\ab{f}~\aofld{⟨\$⟩}~\ab{a₁}
implies \ab{a₀}~\af{≈ᴬ}~\ab{a₁}; we call \ab{f} \defn{surjective} provided
\as{∀}(\AgdaTyped{b}{B})~\as{∃}(\AgdaTyped{a}{A}) such that \ab{f} \aofld{⟨\$⟩} \ab{a} \af{≈ᴮ} \ab{b}.
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
 ∘-IsSurjective fonto gonto {y} = Goal where
  mp : Image g ∋ y → Image g ⟨∘⟩ f ∋ y
  mp (eq c p) = η fonto where
   open Setoid 𝑪 using ( trans )
   η : Image f ∋ c → Image g ⟨∘⟩ f ∋ y
   η (eq a q) = eq a (trans p (cong g q))

  Goal : Image g ⟨∘⟩ f ∋ y
  Goal = mp gonto
\end{code}

\fi

\paragraph*{Factorization of setoid functions\protect\footnote{The code in this paragraph was suggested by an anonymous referee.}}

Any (setoid) function \ab f : \ab A \aor{⟶} \ab B factors as a surjective map
\ab{toIm} : \ab A \aor{⟶} \ab{Im} \ab f followed by an injective map \ab{fromIm} : \ab{Im} \ab f \aor{⟶} \ab B.

\begin{code}

module _ {𝑨 : Setoid α ρᵃ}{𝑩 : Setoid β ρᵇ} where

 Im : (f : 𝑨 ⟶ 𝑩) → Setoid _ _
 Carrier (Im f) = Carrier 𝑨
 _≈ˢ_ (Im f) b1 b2 = f ⟨$⟩ b1 ≈ f ⟨$⟩ b2 where open Setoid 𝑩

 isEquivalence (Im f) = record { refl = refl ; sym = sym; trans = trans }
  where open Setoid 𝑩

 toIm : (f : 𝑨 ⟶ 𝑩) → 𝑨 ⟶ Im f
 toIm f = record { f = id ; cong = cong f }

 fromIm : (f : 𝑨 ⟶ 𝑩) → Im f ⟶ 𝑩
 fromIm f = record { f = λ x → f ⟨$⟩ x ; cong = id }

 fromIm-inj : (f : 𝑨 ⟶ 𝑩) → IsInjective (fromIm f)
 fromIm-inj _ = id

 toIm-surj : (f : 𝑨 ⟶ 𝑩) → IsSurjective (toIm f)
 toIm-surj _ = eq _ (reflˢ 𝑩)

\end{code}

%\paragraph*{Kernels of setoid functions}
%The \defn{kernel} of a function \ab f~\as :~\ab A~\as{→}~\ab B is defined informally by \{\AgdaPair{x}{y} \aod{∈} \ab A \aof{×} \ab A \as : \ab f \ab x \as{=} \ab f \ab y\}. This can be represented in a number of ways, but for our purposes it is convenient to define the kernel as an inhabitant of a (unary) predicate over \ab A \aof{×} \ab A.

%% -------------------------------------------------------------------------------------

\section{Basic Universal Algebra}
\label{basic-universal-algebra}
We now develop a working vocabulary in \mltt corresponding to classical,
single-sorted, set-based universal algebra.
We cover a number of important concepts, but limit ourselves to those
required to prove Birkhoff's HSP theorem.
%\footnote{The concepts we formalize here are just a fraction of those formalized in the \agdaalgebras library.}
In each case, we give a type-theoretic version of the informal definition,
followed by its \agda implementation.

This section is organized into the following subsections:
§\ref{signatures} defines a general type of \emph{signatures} of algebraic structures;
§\ref{algebras} does the same for structures and their products;
§\ref{homomorphisms} defines \emph{homomorphisms}, \emph{monomorphisms}, and \emph{epimorphisms},
presents types that codify these concepts, and formally verifies some of their basic properties;
§\ref{subalgebras}--\ref{terms} do the same for \emph{subalgebras} and \emph{terms}, respectively.

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
Heuristically, the arity \ab{ρ} \ab{f} of an operation symbol \ab{f} \aof{∈} \ab{F} may be
thought of as the number of arguments that \ab{f} takes as ``input.''
%Here (and in the \agdaalgebras library) w
We represent signatures as inhabitants of the following dependent pair type.

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

We need to augment our \af{Signature} type so that it supports algebras over setoid domains.
To do so, following Abel~\cite{Abel:2021}, we
define an operator that translates an ordinary signature into a \defn{setoid signature},
that is, a signature over a setoid domain.
This raises a minor technical issue:
given operations \ab{f} and \ab{g}, with arguments
\ab{u}~\as{:}~\aof{∥}~\ab{𝑆}~\aof{∥}~\ab{f}~\as{→}~\ab{A} and \ab{v}~\as{:}~\aof{∥}~\ab{𝑆}~\aof{∥}~\ab{g}~\as{→}~\ab{A}, respectively, and a proof of \ab{f}~\aod{≡}~\ab{g} (\textit{intensional} equality), we ought to be able to check whether \ab u and \ab v are pointwise
equal. Technically, \ab{u} and \ab{v} appear to inhabit different types; of course, this is reconciled by the hypothesis \ab f \aod{≡} \ab g, as we see in the next definition (borrowed
from~\cite{Abel:2021}).

\begin{code}

EqArgs :  {𝑆 : Signature 𝓞 𝓥}{ξ : Setoid α ρᵃ}
 →        ∀ {f g} → f ≡ g → (∥ 𝑆 ∥ f → Carrier ξ) → (∥ 𝑆 ∥ g → Carrier ξ) → Type (𝓥 ⊔ ρᵃ)
EqArgs {ξ = ξ} ≡.refl u v = ∀ i → u i ≈ v i where open Setoid ξ using ( _≈_ )

\end{code}
\noindent
This makes it possible to define an operator which translates a signature for algebras over bare types into a signature for algebras over setoids.
We denote this operator by \aof{⟨\AgdaUnderscore{}⟩}%
\ifshort
.
\else
 and define it as follows.
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
An \defn{algebraic structure} \ab{𝑨} = (\ab{A}, \ab{Fᴬ}) \defn{in the signature}
\ab{𝑆} = (\ab{F}, \ab{ρ}), or \ab{𝑆}-\defn{algebra}, consists of
\begin{itemize}
\item a type \ab A, called the \defn{domain} of the algebra;
\item a collection \ab{Fᴬ} :=
  \{ \ab{fᴬ} \as{∣} \ab f \aof{∈} \ab F, \ab{fᴬ} \as :
    (\ab{ρ} \ab f \as{→} \ab A) \as{→} \ab A \} of \defn{operations} on \ab{A};
\item a (potentially empty) collection of \defn{identities} satisfied by elements and
operations of \ab{𝑨}.
\end{itemize}
Our \agda implementation represents algebras as inhabitants of a record type with two
fields---a \afld{Domain} setoid denoting the domain of the algebra, and an \afld{Interp} function denoting the interpretation in the algebra of each operation symbol in \ab{𝑆}. We postpone introducing identities until~§\ref{equational-logic}.

\begin{code}

record Algebra α ρ : Type (𝓞 ⊔ 𝓥 ⊔ lsuc (α ⊔ ρ)) where
 field  Domain  : Setoid α ρ
        Interp  : ⟨ 𝑆 ⟩ Domain ⟶ Domain

\end{code}
Thus, for each operation symbol in \ab{𝑆} we have a setoid function
\ab f whose domain is a power of \afld{Domain} and whose codomain is \afld{Domain}.
Further, we define some syntactic sugar to make our formalizations easier to read and reason about. Specifically, if \ab{𝑨} is an algebra, then
\begin{itemize}
\item \aof{𝔻[ \ab{𝑨} ]} denotes the \afld{Domain} setoid of \ab{𝑨},
\item \aof{𝕌[ \ab{𝑨} ]} is the underlying carrier of (the \afld{Domain} setoid of) \ab{𝑨}, and
\item \ab f \aof{̂} \ab{𝑨} denotes the interpretation of the operation symbol \ab f in the algebra \ab{𝑨}.
\end{itemize}
\ifshort %%% BEGIN SHORT VERSION ONLY
 We omit the straightforward formal definitions (\seemedium).
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
%
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
While in some settings, such as category theory, formalizing in \agda
works smoothly with respect to universe levels (see~\cite{agda-categories}), in universal algebra the
terrain is bumpier.
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
\noindent Recall that our \ar{Algebra} type has two universe level parameters, corresponding
to those of the domain setoid.
Concretely, an algebra of type \ar{Algebra} \ab{α} \ab{ρᵃ} has a
\afld{Domain} of type \ar{Setoid} \ab{α} \ab{ρᵃ}. This packages a ``carrier set''
(\afld{Carrier}), inhabiting \ap{Type} \ab{α}, with an equality on \afld{Carrier} of type
\af{Rel} \afld{Carrier} \ab{ρᵃ}.
\fi
\noindent \af{Lift-Alg} takes an algebra parametrized by levels \ab{a} and \ab{ρᵃ}
and constructs a new algebra whose carrier inhabits \ap{Type} (\ab{α} \ap{⊔} \ab{ℓ₀}) and
whose equivalence inhabits \af{Rel}~\afld{Carrier}~(\ab{ρᵃ}~\ap{⊔}~\ab{ℓ₁}).
To be useful, this lifting operation should result in an algebra with the same semantic properties
as the one we started with. We will see in §\ref{sec:lift-alg} that this is indeed the case.

%% -----------------------------------------------------------------------------
\paragraph*{Product Algebras}
We define the \defn{product} of a family of algebras as follows.
Let \ab{ι} be a universe and \ab I~:~\ap{Type}~\ab{ι} a type (the ``indexing type'').
Then \ab{𝒜}~:~\ab I~\as{→}~\ab{Algebra}~\ab{α}~\ab{ρᵃ} represents
an \defn{indexed family of algebras}.
Denote by \af{⨅}~\ab{𝒜} the \defn{product of algebras} in \ab{𝒜} (or \defn{product
algebra}), by which we mean the algebra whose domain is the Cartesian product \af{Π}~\ab
i~꞉~\ab I~\af{,}~\aof{𝔻[~\ab{𝒜}~\ab i~]} of the domains of the algebras in \ab{𝒜}, and
whose operations are those arising from pointwise interpretation in the obvious way: if
\ab{f} is a \ab J-ary operation symbol and if
\ab a~:~\af{Π}~\ab i~꞉~\ab I~\af{,}~\ab J~\as{→}~\aof{𝔻[~\ab{𝒜}~\ab i~]} is, for each
\ab i~:~\ab I, a \ab J-tuple of elements of the domain \aof{𝔻[~\ab{𝒜}~\ab i~]}, then
we define the interpretation of \ab f in \af{⨅}~\ab{𝒜} by\\[-2mm]

(\ab{f}~\af{̂}~\af{⨅}~\ab{𝒜}) \ab a := \as{λ}~(\ab i~:~\ab I)~\as{→}
(\ab{f}~\af{̂}~\ab{𝒜}~\ab i)(\ab{a}~\ab i).\\[8pt]
Here is the formal definition of the product algebra type in \agda.

\begin{code}

module _ {ι : Level}{I : Type ι } where

 ⨅ : (𝒜 : I → Algebra α ρᵃ) → Algebra (α ⊔ ι) (ρᵃ ⊔ ι)

 Domain (⨅ 𝒜) = record  { Carrier = ∀ i → 𝕌[ 𝒜 i ]
                        ; _≈_ = λ a b → ∀ i → (_≈ˢ_ 𝔻[ 𝒜 i ]) (a i)(b i)
                        ; isEquivalence =
                           record  { refl = λ i → reflᵉ (isEquivalence 𝔻[ 𝒜 i ])
                                   ; sym = λ x i → symᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)
                                   ; trans = λ x y i → transᵉ (isEquivalence 𝔻[ 𝒜 i ])(x i)(y i) }}

 Interp (⨅ 𝒜) ⟨$⟩ (f , a) = λ i → (f ̂ (𝒜 i)) (flip a i)
 cong (Interp (⨅ 𝒜)) (≡.refl , f=g ) = λ i → cong (Interp (𝒜 i)) (≡.refl , flip f=g i )

\end{code}
\noindent Evidently, the carrier of the product algebra type is indeed the (dependent)
product of the carriers in the indexed family. The rest of the definitions are the ``pointwise''
versions of the underlying ones.

%% -------------------------------------------------------------------------------------
%\subsection{Homomorphisms}\label{homomorphisms}
\subsection{Structure preserving maps and isomorphism}\label{homomorphisms}
Throughout the rest of the paper, unless stated otherwise, \ab{𝑨} and \ab{𝑩}
will denote \ab{𝑆}-algebras inhabiting the types \af{Algebra} \ab{α} \ab{ρᵃ} and
\af{Algebra} \ab{β} \ab{ρᵇ}, respectively.

A \defn{homomorphism} (or ``hom'') from
\ab{𝑨} to \ab{𝑩} is a setoid function \ab{h}~:~\aof{𝔻[~\ab{𝑨}~]} \aor{⟶} \aof{𝔻[~\ab{𝑩}~]}
that is \defn{compatible} with all basic operations; that is, for
every operation symbol \ab{f} : \af{∣~\ab{𝑆}~∣} and all tuples
\ab{a} : \af{∥~\ab{𝑆}~∥}~\ab{f} \as{→} \aof{𝕌[~\ab{𝑨}~]}, we have \ab{h} \aofld{⟨\$⟩}
(\ab{f}~\af{̂}~\ab{𝑨}) \ab{a} \af{≈}
(\ab{f}~\af{̂}~\ab{𝑩}) \as{λ} \ab x \as{→} \ab h \AgdaOperator{\AgdaField{⟨\$⟩}} (\ab a \ab x).

It is convenient to first formalize ``compatible'' (\af{compatible-map-op}),
representing the assertion that a given setoid function
\ab{h}~:~\aof{𝔻[~\ab{𝑨}~]} \aor{⟶} \aof{𝔻[~\ab{𝑩}~]} commutes with a given
operation symbol \ab{f}, and then generalize over operation symbols
to yield the type (\af{compatible-map}) of compatible maps from (the domain of)
\ab{𝑨} to (the domain of) \ab{𝑩}.

\begin{code}

module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where

 compatible-map-op : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → ∣ 𝑆 ∣ → Type _
 compatible-map-op h f = ∀ {a} → h ⟨$⟩ (f ̂ 𝑨) a ≈ (f ̂ 𝑩) λ x → h ⟨$⟩ (a x)
  where open Setoid 𝔻[ 𝑩 ] using ( _≈_ )

 compatible-map : (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) → Type _
 compatible-map h = ∀ {f} → compatible-map-op h f

\end{code}
Using these we define the property (\ar{IsHom}) of being a homomorphism, and
finally the type (\af{hom}) of homomorphisms from \ab{𝑨} to \ab{𝑩}.

\begin{code}

 record IsHom (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵇ) where
  constructor  mkhom
  field        compatible : compatible-map h

 hom : Type _
 hom = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsHom

\end{code}
Thus, an inhabitant of \af{hom} is a pair (\ab h , \ab p) consisting of
a setoid function \ab h, from the domain of \ab{𝑨} to that of \ab{𝑩}, along with
a proof \ab p that \ab h is a homomorphism.

A \defn{monomorphism} (resp. \defn{epimorphism}) is an injective (resp. surjective)
homomorphism. The \agdaalgebras library defines predicates \ar{IsMon} and \ar{IsEpi} for these,
as well as \af{mon} and \af{epi} for the corresponding types.

\begin{code}

 record IsMon (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ ρᵇ) where
  field  isHom : IsHom h
         isInjective : IsInjective h
  HomReduct : hom
  HomReduct = h , isHom

 mon : Type _
 mon = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsMon

\end{code}
\noindent As with \af{hom}, the type \af{mon} is a dependent product type; each inhabitant is a pair
consisting of a setoid function, say, \ab h, along with a proof that \ab h is a monomorphism.

\begin{code}

 record IsEpi (h : 𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ β ⊔ ρᵇ) where
  field  isHom : IsHom h
         isSurjective : IsSurjective h
  HomReduct : hom
  HomReduct = h , isHom

 epi : Type _
 epi = Σ (𝔻[ 𝑨 ] ⟶ 𝔻[ 𝑩 ]) IsEpi
\end{code}

\ifshort\else
Here are two utilities that are useful for translating between types.

\begin{code}
open IsHom ; open IsMon ; open IsEpi
module _ (𝑨 : Algebra α ρᵃ)(𝑩 : Algebra β ρᵇ) where
 mon→intohom : mon 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣
 mon→intohom (hh , hhM) = (hh , isHom hhM) , isInjective hhM

 epi→ontohom : epi 𝑨 𝑩 → Σ[ h ∈ hom 𝑨 𝑩 ] IsSurjective ∣ h ∣
 epi→ontohom (hh , hhE) = (hh , isHom hhE) , isSurjective hhE
\end{code}
%% -----------------------------------------------------------------------------
\fi

\paragraph*{Composition of homomorphisms}
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
  ∘-is-hom ghom hhom = mkhom c where
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
%% -----------------------------------------------------------------------------
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
%% -----------------------------------------------------------------------------
\paragraph*{Homomorphisms of product algebras}
Suppose we have an algebra \ab{𝑨}, a type \ab I : \ap{Type} \ab{𝓘}, and a family \ab{ℬ} :
\ab I \as{→} \ar{Algebra} \ab{β} \ab{ρᵇ} of algebras.
We sometimes refer to the inhabitants of \ab{I} as \emph{indices}, and call \ab{ℬ} an
\defn{indexed family of algebras}. If in addition we have a family \ab{𝒽} : (\ab i : \ab
I) → \af{hom} \ab{𝑨} (\ab{ℬ} \ab i) of homomorphisms, then we can construct a homomorphism
from \ab{𝑨} to the product \af{⨅} \ab{ℬ} in the natural way.  We codify the latter in
dependent type theory as follows.

\begin{code}

module _ {ι : Level}{I : Type ι}{𝑨 : Algebra α ρᵃ}(ℬ : I → Algebra β ρᵇ) where
 ⨅-hom-co : (∀(i : I) → hom 𝑨 (ℬ i)) → hom 𝑨 (⨅ ℬ)
 ⨅-hom-co 𝒽 = h , hhom where  h : 𝔻[ 𝑨 ] ⟶ 𝔻[ ⨅ ℬ ]
                              h ⟨$⟩ a = λ i → ∣ 𝒽 i ∣ ⟨$⟩ a
                              cong h xy i = cong ∣ 𝒽 i ∣ xy
                              hhom : IsHom 𝑨 (⨅ ℬ) h
                              compatible hhom = λ i → compatible ∥ 𝒽 i ∥
\end{code}
\fi

Two structures are \defn{isomorphic} provided there are homomorphisms from each to the
other that compose to the identity. We define the following record type to represent this concept.
%We represent this notion by the type \ar{\au{}≅\au{}}.
\ifshort
\else
Note that the definition, shown below, includes a proof of the fact that the maps \afld{to} and
\afld{from} are bijective, which makes this fact more accessible.
\fi

\begin{code}

module _ (𝑨 : Algebra α ρᵃ) (𝑩 : Algebra β ρᵇ) where
 open Setoid 𝔻[ 𝑨 ]  using ()  renaming ( _≈_ to _≈ᴬ_ )
 open Setoid 𝔻[ 𝑩 ]  using ()  renaming ( _≈_ to _≈ᴮ_ )

 record _≅_ : Type (𝓞 ⊔ 𝓥 ⊔ α ⊔ ρᵃ ⊔ β ⊔ ρᵇ ) where
  constructor  mkiso
  field        to    : hom 𝑨 𝑩
               from  : hom 𝑩 𝑨
               to∼from : ∀ b → ∣ to ∣    ⟨$⟩ (∣ from ∣  ⟨$⟩ b)  ≈ᴮ b
               from∼to : ∀ a → ∣ from ∣  ⟨$⟩ (∣ to ∣    ⟨$⟩ a)  ≈ᴬ a

\end{code}
\ifshort
The \agdaalgebras library also includes formal proof that the \afld{to} and \afld{from} maps are bijections and that \ar{\au{}≅\au{}} is an equivalence relation, but we suppress these details.
\else
\begin{code}

  toIsInjective : IsInjective ∣ to ∣
  toIsInjective {x}{y} xy = trans (sym (from∼to x)) (trans ξ (from∼to y))
   where  open Setoid 𝔻[ 𝑨 ] using ( sym ; trans )
          ξ : ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ x) ≈ᴬ ∣ from ∣ ⟨$⟩ (∣ to ∣ ⟨$⟩ y)
          ξ = cong ∣ from ∣ xy

  fromIsSurjective : IsSurjective ∣ from ∣
  fromIsSurjective {x} = eq (∣ to ∣ ⟨$⟩ x) (sym (from∼to x))
   where open Setoid 𝔻[ 𝑨 ] using ( sym )

open _≅_

\end{code}

It is easy to prove that \ar{\au{}≅\au{}} is an equivalence relation, as follows.

\begin{code}

≅-refl : Reflexive (_≅_ {α}{ρᵃ})
≅-refl {α}{ρᵃ}{𝑨} = mkiso 𝒾𝒹 𝒾𝒹 (λ b → refl) λ a → refl where open Setoid 𝔻[ 𝑨 ] using ( refl )
≅-sym : Sym (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ})
≅-sym φ = mkiso (from φ) (to φ) (from∼to φ) (to∼from φ)

≅-trans : Trans (_≅_ {α}{ρᵃ}) (_≅_{β}{ρᵇ}) (_≅_{α}{ρᵃ}{γ}{ρᶜ})
≅-trans {ρᶜ = ρᶜ}{𝑨}{𝑩}{𝑪} ab bc = mkiso f g τ ν where
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
%% -----------------------------------------------------------------------------
\paragraph*{Homomorphic images}
We have found that a useful way to encode the concept of \emph{homomorphic image}
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

IdHomImage : {𝑨 : Algebra α ρᵃ} → 𝑨 IsHomImageOf 𝑨
IdHomImage {α = α}{𝑨 = 𝑨} = 𝒾𝒹 , λ {y} → Image_∋_.eq y refl
 where open Setoid 𝔻[ 𝑨 ] using ( refl )
\end{code}
%\noindent These types should be self-explanatory, but just to be sure, we pause
%to describe the semantics of the Sigma type appearing in the definition of \af{HomImages}.
%If \ab{𝑨} : \af{Algebra} \ab{α} \ab{ρᵃ} is an \ab{𝑆}-algebra, then \af{HomImages} \ab{𝑨}
%denotes the type of pairs (\ab{𝑩} \aic{,} \ab p) such that \ab{𝑩} : \ar{Algebra} \ab{β} \ab{ρᵇ}
%and \ab p is a proof that there exists a hom from \ab{𝑨} onto \ab{𝑩}.

%% -----------------------------------------------------------------------------
\paragraph*{Factorization of homomorphisms}
Another theorem in the \agdaalgebras library, called \af{HomFactor}, formalizes the following factorization result: if \ab g : \af{hom}
\ab{𝑨} \ab{𝑩}, \ab h : \af{hom} \ab{𝑨} \ab{𝑪}, \ab h is surjective, and \af{ker} \ab h
\aof{⊆} \af{ker} \ab g, then there exists \ab{φ} : \af{hom} \ab{𝑪} \ab{𝑩} such that \ab g = \ab{φ} \aof{∘} \ab h.
A special case of this result that we use below is the fact that the setoid function factorization we saw above %---\ab f = %: \ab A \aor{⟶} \ab B factors as a surjective map
%\ab{fromIm} \aof{∘} \ab{toIm}---% : \ab A \aor{⟶} \ab{Im} \ab f followed by an injective map \ab{fromIm} : \ab{Im} \ab f \aor{⟶} \ab B.
lifts to factorization of homomorphisms. Moreover, we associate a homomorphism \ab h with its image---which is (the domain of) a subalgebra of the codomain of \ab h---using the function \ab{HomIm} defined below.\footnote{The definition of \ab{HomIm} was provided by an anonymous referee; it is indeed simpler than the general \af{HomFactor} theorem.}

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} where

 HomIm : (h : hom 𝑨 𝑩) → Algebra _ _
 Domain (HomIm h) = Im ∣ h ∣
 Interp (HomIm h) ⟨$⟩ (f , la) = (f ̂ 𝑨) la
 cong (Interp (HomIm h)) {x1 , x2} {.x1 , y2} (≡.refl , e) =
  begin
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , x2))  ≈⟨ h-compatible                  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ x2 x)       ≈⟨ cong (Interp 𝑩) (≡.refl , e)  ⟩
   Interp 𝑩  ⟨$⟩ (x1 , λ x → ∣ h ∣  ⟨$⟩ y2 x)       ≈˘⟨ h-compatible                 ⟩
      ∣ h ∣  ⟨$⟩         (Interp 𝑨  ⟨$⟩ (x1 , y2))  ∎
   where  open Setoid 𝔻[ 𝑩 ] ; open SetoidReasoning 𝔻[ 𝑩 ]
          open IsHom ∥ h ∥ renaming (compatible to h-compatible)

 toHomIm : (h : hom 𝑨 𝑩) → hom 𝑨 (HomIm h)
 toHomIm h = toIm ∣ h ∣ , mkhom (reflˢ 𝔻[ 𝑩 ])

 fromHomIm : (h : hom 𝑨 𝑩) → hom (HomIm h) 𝑩
 fromHomIm h = fromIm ∣ h ∣ , mkhom (IsHom.compatible ∥ h ∥)
\end{code}



%% -----------------------------------------------------------------------------
\subsection{Lift-Alg is an algebraic invariant}\label{sec:lift-alg}
The \af{Lift-Alg} operation neatly resolves the technical problem of
universe non-cumulativity because isomorphism classes of algebras are closed under \af{Lift-Alg}.

\begin{code}

module _ {𝑨 : Algebra α ρᵃ}{ℓ : Level} where
 Lift-≅ˡ : 𝑨 ≅ (Lift-Algˡ 𝑨 ℓ)
 Lift-≅ˡ = mkiso ToLiftˡ FromLiftˡ (ToFromLiftˡ{𝑨 = 𝑨}) (FromToLiftˡ{𝑨 = 𝑨}{ℓ})
 Lift-≅ʳ : 𝑨 ≅ (Lift-Algʳ 𝑨 ℓ)
 Lift-≅ʳ = mkiso ToLiftʳ FromLiftʳ (ToFromLiftʳ{𝑨 = 𝑨}) (FromToLiftʳ{𝑨 = 𝑨}{ℓ})

Lift-≅ : {𝑨 : Algebra α ρᵃ}{ℓ ρ : Level} → 𝑨 ≅ (Lift-Alg 𝑨 ℓ ρ)
Lift-≅ = ≅-trans Lift-≅ˡ Lift-≅ʳ
\end{code}
%% -------------------------------------------------------------------------------------
\subsection{Subalgebras}
\label{subalgebras}
%Given \ab{𝑆}-algebras \ab{𝑨} and \ab{𝑩},
We say that \ab{𝑨} is a \defn{subalgebra} of
\ab{𝑩} and write \ab{𝑨}~\aof{≤}~\ab{𝑩} just in case \ab{𝑨} can be \emph{homomorphically
embedded} in \ab{𝑩}; in other terms, \ab{𝑨}~\aof{≤}~\ab{𝑩} iff there exists an injective
hom from \ab{𝑨} to \ab{𝑩}.

\begin{code}

_≤_ : Algebra α ρᵃ → Algebra β ρᵇ → Type _
𝑨 ≤ 𝑩 = Σ[ h ∈ hom 𝑨 𝑩 ] IsInjective ∣ h ∣

\end{code}
The subalgebra relation is reflexive, by the identity monomorphism (and transitive by composition of monomorphisms, hence, a \defn{preorder}, though we won't need this fact here).

\begin{code}

≤-reflexive   :  {𝑨 : Algebra α ρᵃ} → 𝑨 ≤ 𝑨
≤-reflexive = 𝒾𝒹 , id

\end{code}
%≤-transitive  :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} → 𝑨 ≤ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
%≤-transitive ( f , finj ) ( g , ginj ) = (∘-hom f g ) , ∘-IsInjective ∣ f ∣ ∣ g ∣ finj ginj
If
\ab{𝒜} : \ab I → \af{Algebra} \ab{α} \ab{ρᵃ},
\ab{ℬ} : \ab I → \af{Algebra} \ab{β} \ab{ρᵇ} (families of \ab{𝑆}-algebras) and if
\ab{ℬ} \ab i \af{≤} \ab{𝒜} \ab i for all \ab i~:~\ab I, then \af{⨅} \ab{ℬ} is a subalgebra
of \af{⨅} \ab{𝒜}. Below we will use \af{⨅-≤} to denote this fact.

We conclude this section with an easy fact that will be useful later;
it simply converts a monomorphism into a proof of a subalgebra relationship.
%The first converts a monomorphism to a subalgebra witness while the second is an algebraic invariance property of \aof{≤}.

\begin{code}

mon→≤ : {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ} → mon 𝑨 𝑩 → 𝑨 ≤ 𝑩
mon→≤ {𝑨 = 𝑨}{𝑩} x = mon→intohom 𝑨 𝑩 x
\end{code}
%≅-trans-≤ :  {𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{𝑪 : Algebra γ ρᶜ} → 𝑨 ≅ 𝑩 → 𝑩 ≤ 𝑪 → 𝑨 ≤ 𝑪
%≅-trans-≤ A≅B (h , hinj) = (∘-hom (to A≅B) h) , (∘-IsInjective ∣ to A≅B ∣ ∣ h ∣ (toIsInjective A≅B) hinj)


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
follows: %(cf.~\cite[Def. 4.19]{Bergman:2012}):
\ab{𝑇₀} := \ab X \aof{∪} \ab{S₀} and
\ab{𝑇ₙ₊₁} := \ab{𝑇ₙ} \aof{∪} \ab{𝒯ₙ}, where \ab{𝒯ₙ} is the collection of all \ab f \ab t
such that \ab f : \aof{∣~\ab{𝑆}~∣} and \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→}
\ab{𝑇ₙ}.
\ifshort\else
(Recall, \aof{∥~\ab{𝑆}~∥} \ab f is the arity of the operation symbol \ab f.)
\fi
An \ab{𝑆}-\defn{term} is a term in the language of \ab{𝑆} and the collection of all
\ab{𝑆}-\defn{terms} in the context \ab X is \Term{X} := \aof{⋃ₙ} \ab{𝑇ₙ}.

In type theory, this translates to two cases: variable injection and applying an
operation symbol to a tuple of terms. This represents each term as a tree
with an operation symbol at each \aic{node} and a variable symbol at each leaf \aic{ℊ};
hence the constructor names (\aic{ℊ} for ``generator'' and \aic{node} for ``node'') in the
following inductively defined type.

\begin{code}

data Term (X : Type χ) : Type (ov χ)  where
 ℊ : X → Term X
 node : (f : ∣ 𝑆 ∣)(t : ∥ 𝑆 ∥ f → Term X) → Term X
\end{code}
%% -----------------------------------------------------------------------------
\paragraph*{The term algebra}
We enrich the \ad{Term} type to a setoid of  \ab{𝑆}-terms, which will ultimately
be the domain of an algebra, called the \emph{term algebra in the signature} \ab{𝑆}.
For this we need an equivalence relation on terms.

\begin{code}

module _ {X : Type χ } where

 data _≃_ : Term X → Term X → Type (ov χ) where
  rfl : {x y : X} → x ≡ y → (ℊ x) ≃ (ℊ y)
  gnl : ∀ {f}{s t : ∥ 𝑆 ∥ f → Term X} → (∀ i → (s i) ≃ (t i)) → (node f s) ≃ (node f t)

\end{code}
\ifshort
Below we denote by \af{≃-isEquiv} the easy (omitted) proof that \ad{\au{}≃\au{}} is an equivalence relation.
\else
It is easy to show that \ad{\au{}≃\au{}} is an equivalence relation as follows.

\begin{code}

 ≃-isRefl   : Reflexive      _≃_
 ≃-isRefl {ℊ _} = rfl ≡.refl
 ≃-isRefl {node _ _} = gnl λ _ → ≃-isRefl

 ≃-isSym    : Symmetric      _≃_
 ≃-isSym (rfl x) = rfl (≡.sym x)
 ≃-isSym (gnl x) = gnl λ i → ≃-isSym (x i)

 ≃-isTrans  : Transitive     _≃_
 ≃-isTrans (rfl x) (rfl y) = rfl (≡.trans x y)
 ≃-isTrans (gnl x) (gnl y) = gnl λ i → ≃-isTrans (x i) (y i)

 ≃-isEquiv  : IsEquivalence  _≃_
 ≃-isEquiv = record { refl = ≃-isRefl ; sym = ≃-isSym ; trans = ≃-isTrans }
\end{code}
\fi

For a given signature \ab{𝑆} and context \ab X,
%if the type \Term{X} is nonempty (equivalently, if \ab X or
%\aof{∣~\ab{𝑆}~∣} is nonempty), then
we define the algebra \T{X}, known as the \defn{term algebra in} \ab{𝑆} \defn{over} \ab
X.
%Terms are viewed as acting on other terms, so both
%the elements of the domain of \T{X}
%and its basic operations are terms themselves.
The domain of \T{X} is \Term{X} and, for each operation symbol \ab
f : \aof{∣~\ab{𝑆}~∣}, we define \ab f~\aof{̂}~\T{X} to be the operation which maps
each tuple \ab t : \aof{∥~\ab{𝑆}~∥} \ab f \as{→} \Term{X} of terms to the formal
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
%% -----------------------------------------------------------------------------
%\paragraph*{Substitution, environments and interpretation of terms}
\paragraph*{Environments and interpretation of terms}

\begin{comment}
Recall that the domain of an algebra \ab{𝑨} is a setoid, which we denote by \af{𝔻[~\ab{𝑨}~]}, whose carrier is that of \ab{𝑨} (denoted \af{𝕌[~\ab{𝑨}~]}) and whose equivalence relation represents equality of elements in \af{𝕌[~\ab{𝑨}~]}. \af{Sub} performs substitution from one context to another; specifically, if \ab X, \ab Y are contexts, then \af{Sub} \ab X \ab Y assigns a term in \ab X to each symbol in \ab Y.
begin{code}
-- Sub : Type χ → Type χ → Type _
-- Sub X Y = (y : Y) → Term X
end{code}
A substitution \ab{σ} applied to a term \ab t is denoted by \af{[~\ab{σ}~]} \ab t.
begin{code}
-- [_]_ : {X Y : Type χ} → Sub X Y → Term Y → Term X
-- [ σ ] (ℊ x) = σ x
-- [ σ ] (node f ts) = node f λ i → [ σ ] (ts i)
end{code}
\end{comment}
Fix a signature \ab{𝑆} and a context \ab X.
%The next two types are defined relative to a fixed \ab{𝑆}-algebra, say, \ab{𝑨}, so
%we place them in a submodule that takes the algebra as given.
An \defn{environment} for \ab{𝑨} and \ab X is a setoid whose carrier is a mapping from the variable symbols \ab X to the domain \AgdaOperator{\AgdaFunction{𝕌[}}~\AgdaBound{𝑨}~\AgdaOperator{\AgdaFunction{]}} and whose equivalence relation is pointwise equality. Our formalization of this concept is the same as that of~\cite{Abel:2021}, which Abel uses to formalize Birkhoff's completeness theorem.

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
The \defn{interpretation} of a term \emph{evaluated} in a particular environment is defined as follows.

\begin{code}

 ⟦_⟧ : {X : Type χ}(t : Term X) → (Env X) ⟶ 𝔻[ 𝑨 ]
 ⟦ ℊ x ⟧          ⟨$⟩ ρ    = ρ x
 ⟦ node f args ⟧  ⟨$⟩ ρ    = (Interp 𝑨) ⟨$⟩ (f , λ i → ⟦ args i ⟧ ⟨$⟩ ρ)
 cong ⟦ ℊ x ⟧ u≈v          = u≈v x
 cong ⟦ node f args ⟧ x≈y  = cong (Interp 𝑨)(≡.refl , λ i → cong ⟦ args i ⟧ x≈y )

\end{code}
Two terms are proclaimed \defn{equal} if they are equal for all environments.

\begin{code}

 Equal : {X : Type χ}(s t : Term X) → Type _
 Equal {X = X} s t = ∀ (ρ : Carrier (Env X)) → ⟦ s ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ ρ

\end{code}
Proof that \af{Equal} is an equivalence relation, and that the implication \ab
s~\af{≃}~\ab t \as{→} \af{Equal} \ab s \ab t holds for all terms \ab s and \ab t,
is also found in~\cite{Abel:2021}.
\ifshort
We denote the latter %-- proofs of these facts by \af{EqualIsEquiv} and 
by \af{≃→Equal} in the sequel.
\else
We reproduce them here to keep the paper self-contained.
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
\begin{comment}
Another useful fact we will need is that substitution and evaluation commute; that is, applying substitution \ab{σ} to a term \ab{t} and evaluating the result in environment \ab{ρ} has the same effect as evaluating \ab{t} in the environment \as{λ} \ab x \as{→} \aof{⟦~\ab{σ}~\ab{x}~⟧}~\aofld{⟨\$⟩} \ab{ρ} (see~\cite{Abel:2021} or~\cite[Lem.~3.3.11]{Mitchell:1996}).
begin{code}
 -- substitution :  {X Y : Type χ} → (t : Term Y) (σ : Sub X Y) (ρ : Carrier( Env X ) )
 --  →              ⟦ [ σ ] t ⟧ ⟨$⟩ ρ ≈ ⟦ t ⟧ ⟨$⟩ (λ x → ⟦ σ x ⟧ ⟨$⟩ ρ)
 -- substitution    (ℊ x)        σ ρ = refl
 -- substitution    (node f ts)  σ ρ = cong (Interp 𝑨)(≡.refl , λ i → substitution (ts i) σ ρ)
end{code}
\end{comment}
%% -----------------------------------------------------------------------------

\paragraph*{Compatibility of terms}
We need to formalize two more concepts involving terms.
The first (\af{comm-hom-term}) is the assertion that every term commutes with every homomorphism, and
the second (\af{interp-prod}) is the interpretation of a term in a product algebra.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}(hh : hom 𝑨 𝑩) where
 open Environment 𝑨  using ( ⟦_⟧ )
 open Environment 𝑩  using () renaming ( ⟦_⟧ to ⟦_⟧ᴮ )
 open Setoid 𝔻[ 𝑩 ]  using ( _≈_ ; refl  )
 private hfunc = ∣ hh ∣ ; h = _⟨$⟩_ hfunc

 comm-hom-term : (t : Term X) (a : X → 𝕌[ 𝑨 ]) → h (⟦ t ⟧ ⟨$⟩ a) ≈ ⟦ t ⟧ᴮ ⟨$⟩ (h ∘ a)
 comm-hom-term (ℊ x) a = refl
 comm-hom-term (node f t) a =  begin
   h(⟦ node f t ⟧ ⟨$⟩ a)            ≈⟨ compatible ∥ hh ∥ ⟩
   (f ̂ 𝑩)(λ i → h(⟦ t i ⟧ ⟨$⟩ a))  ≈⟨ cong(Interp 𝑩)(≡.refl , λ i → comm-hom-term(t i) a) ⟩
   ⟦ node f t ⟧ᴮ ⟨$⟩ (h ∘ a)   ∎ where open SetoidReasoning 𝔻[ 𝑩 ]

module _ {X : Type χ}{ι : Level} {I : Type ι} (𝒜 : I → Algebra α ρᵃ) where
 open Setoid 𝔻[ ⨅ 𝒜 ]  using ( _≈_ )
 open Environment      using ( ⟦_⟧ ; ≃→Equal )

 interp-prod : (p : Term X) → ∀ ρ →  (⟦ ⨅ 𝒜 ⟧ p) ⟨$⟩ ρ   ≈   λ i → (⟦ 𝒜 i ⟧ p) ⟨$⟩ λ x → (ρ x) i
 interp-prod (ℊ x)       = λ ρ i  → ≃→Equal (𝒜 i) (ℊ x) (ℊ x) ≃-isRefl λ _ → (ρ x) i
 interp-prod (node f t)  = λ ρ    → cong (Interp (⨅ 𝒜)) ( ≡.refl , λ j k → interp-prod (t j) ρ k )
\end{code}

\section{Equational Logic}
\label{equational-logic}
%% -----------------------------------------------------------------------------
\paragraph*{Term identities, equational theories, and the ⊧ relation}
%Given a signature \ab{𝑆} and a context \ab X,
An \ab{𝑆}-\defn{term equation} (or \ab{𝑆}-\defn{term identity})
is an ordered pair (\ab p , \ab q) of 𝑆-terms, also denoted by \ab p \af{≈} \ab q.
%They are often simply called equations or identities, especially when the signature \ab{𝑆} is evident.
We define an \defn{equational theory} (or \defn{algebraic theory}) to be a pair \ab{T} =
(\ab{𝑆} , \ab{ℰ}) consisting of a signature \ab{𝑆} and a collection \ab{ℰ} of
\ab{𝑆}-term equations.\footnote{Some authors reserve the term \defn{theory} for
a \emph{deductively closed} set of equations, that is, a set of equations that is closed
under entailment.}

We say that the algebra \ab{𝑨} \defn{models} the identity \ab{p}~\af{≈}~\ab{q} and we write
\ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q}
if for all \ab{ρ} : \ab X \as{→} \aof{𝔻[~\ab{𝑨}~]}
we have \aof{⟦~\ab{p}~⟧} \aofld{⟨\$⟩} \ab{ρ} \af{≈} \aof{⟦~\ab{q}~⟧} \aofld{⟨\$⟩} \ab{ρ}.
In other words, when interpreted in the algebra \ab{𝑨},
the terms \ab{p} and \ab{q} are equal no matter what values are assigned to variable symbols occurring in \ab{p} and \ab{q}.
If \ab{𝒦} is a class of algebras of a given signature, then we write \ab{𝒦}~\aof{⊫}~\ab{p}~\aof{≈}~\ab{q}
and say that \ab{𝒦} \defn{models} the identity \ab{p}~\af{≈}~\ab{q} provided \ab{𝑨}~\aof{⊧}~\ab{p}~\aof{≈}~\ab{q} for every \ab{𝑨} \aof{∈} \ab{𝒦}.

\begin{code}

module _ {X : Type χ} where
 _⊧_≈_ : Algebra α ρᵃ → Term X → Term X → Type _
 𝑨 ⊧ p ≈ q = Equal p q where open Environment 𝑨

 _⊫_≈_ : Pred (Algebra α ρᵃ) ℓ → Term X → Term X → Type _
 𝒦 ⊫ p ≈ q = ∀ 𝑨 → 𝒦 𝑨 → 𝑨 ⊧ p ≈ q

\end{code}
We represent a set of term identities as a predicate over pairs of terms,
\ifshort\else
say, \ab{ℰ} : \af{Pred}(\ad{Term} \ab{X} \af{×} \ad{Term} \ab{X})~\au{}
\fi
and we denote by \ab{𝑨}~\aof{⊨}~\ab{ℰ} the assertion that \ab{𝑨} models \ab{p}~\af{≈}~\ab{q}
for all (\ab{p} , \ab{q}) \af{∈} \ab{ℰ}.%
\ifshort\else\footnote{\af{⊨} is a stretched version of the models symbol, \af{⊧},
so \agda can distinguish between the two.and parse expressions involving the types
\af{\au{}⊨\au{}} and \af{\au{}⊧\au{}≈\au{}}.
In Emacs \texttt{agda2-mode}, the symbol \af{⊨} is produced by typing
\textbackslash\textbar{}=, while \af{⊧} is produced with \textbackslash{}models.}
\fi

\begin{code}

 _⊨_ : (𝑨 : Algebra α ρᵃ) → Pred(Term X × Term X)(ov χ) → Type _
 𝑨 ⊨ ℰ = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨

\end{code}
An important property of the binary relation \aof{⊧} is \emph{algebraic invariance} (i.e.,
invariance under isomorphism).  We formalize this result as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(𝑩 : Algebra β ρᵇ)(p q : Term X) where
 ⊧-I-invar : 𝑨 ⊧ p ≈ q  →  𝑨 ≅ 𝑩  →  𝑩 ⊧ p ≈ q
 ⊧-I-invar Apq (mkiso fh gh f∼g g∼f) ρ = begin
  ⟦ p ⟧     ⟨$⟩             ρ    ≈˘⟨  cong ⟦ p ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ p ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈˘⟨  comm-hom-term fh p (g ∘ ρ)  ⟩
  f(⟦ p ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   cong ∣ fh ∣ (Apq (g ∘ ρ))   ⟩
  f(⟦ q ⟧ᴬ  ⟨$⟩       (g ∘  ρ))  ≈⟨   comm-hom-term fh q (g ∘ ρ)  ⟩
  ⟦ q ⟧     ⟨$⟩ (f ∘  (g ∘  ρ))  ≈⟨   cong ⟦ q ⟧ (f∼g ∘ ρ)        ⟩
  ⟦ q ⟧     ⟨$⟩             ρ    ∎
  where  private f = _⟨$⟩_ ∣ fh ∣ ; g = _⟨$⟩_ ∣ gh ∣
         open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ )
         open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

\end{code}
If \ab{𝒦} is a class of \ab{𝑆}-algebras, the set of identities modeled by \ab{𝒦}, denoted \af{Th}~\ab{𝒦}, is called the \defn{equational theory} of \ab{𝒦}. If \ab{ℰ} is a set of \ab{𝑆}-term identities,
the class of algebras modeling \ab{ℰ}, denoted \af{Mod}~\ab{ℰ}, is called the \defn{equational class axiomatized} by \ab{ℰ}. We codify these notions in the next two definitions.

\begin{code}

Th : {X : Type χ} → Pred (Algebra α ρᵃ) ℓ → Pred(Term X × Term X) _
Th 𝒦 = λ (p , q) → 𝒦 ⊫ p ≈ q

Mod : {X : Type χ} → Pred(Term X × Term X) ℓ → Pred (Algebra α ρᵃ) _
Mod ℰ 𝑨 = ∀ {p q} → (p , q) ∈ ℰ → Equal p q where open Environment 𝑨
\end{code}

\begin{comment}
\paragraph*{Entailment}
If \ab{ℰ} is a set of identities and \ab{p} and \ab{q} are terms,
we say that \ab{ℰ} \defn{entails} \ab{p}~\aof{≈}~\ab{q} and write
\ab{ℰ}~\ad{⊢}~\ab{p}~\ad{≈}~\ab{q} just in case every model of \ab{ℰ} also models
\ab{p}~\aof{≈}~\ab{q}.
We base our definition of \defn{entailment type} on the one in~\cite{Abel:2021}.  It contains cases for representing hypotheses, congruence of term
application, that substitution respects entailment, and that entailment is
an equivalence.
begin{code}
end{code}
The fact that this represents the informal semantic notion of entailment given earlier is called \defn{soundness} and \defn{completeness}. More precisely, \defn{the entailment type is sound} means that \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\ad{≈}~\ab q only if \ab p \aof{≈} \ab q in every model of \ab{ℰ}. \defn{The entailment type is complete} means \ab p \aof{≈} \ab q in every model of \ab{ℰ} only if \ab{ℰ}~\ad{⊢}~\ab{X}~\ad{▹}~\ab p~\aof{≈}~\ab q.
We will use soundness of entailment only once below~(by the name \af{sound}), so we omit its proof (but see~\cite{Abel:2021} for details).
\end{comment}

%% -----------------------------------------------------------------------------
\paragraph*{The Closure Operators H, S, P and V}
Fix a signature \ab{𝑆}, let \ab{𝒦} be a class of \ab{𝑆}-algebras, and define
\begin{itemize}
\item \af H \ab{𝒦} := the class of all homomorphic images of members of \ab{𝒦};
\item \af S \ab{𝒦} := the class of all subalgebras of members of \ab{𝒦};
\item \af P \ab{𝒦} := the class of all products of members of \ab{𝒦}.
\end{itemize}
\af H, \af S, and \af P are \emph{closure operators} (expansive, monotone, and
idempotent).  A class \ab{𝒦} of \ab{𝑆}-algebras is said to be \emph{closed under
the taking of homomorphic images} provided \af H \ab{𝒦} \aof{⊆} \ab{𝒦}. Similarly, \ab{𝒦} is
\emph{closed under the taking of subalgebras} (resp., \emph{arbitrary products}) provided
\af S~\ab{𝒦}~\aof{⊆}~\ab{𝒦} (resp., \af P \ab{𝒦} \aof{⊆} \ab{𝒦}). The operators \af H, \af
S, and \af P can be composed with one another repeatedly, forming yet more closure
operators. We represent these three closure operators in type theory as follows.

\begin{comment}
An algebra is a homomorphic image (resp., subalgebra; resp., product) of every algebra to which it is isomorphic.
Thus, the class \af H \ab{𝒦} (resp., \af S \ab{𝒦}; resp., \af P \ab{𝒦}) is closed under isomorphism.
We now define the type \af H to represent classes of algebras that include all homomorphic images
of algebras in the class---i.e., classes that are closed under the taking of homomorphic
images---the type \af S to represent classes of algebras that closed under the taking of subalgebras,
and the type \af P to represent classes of algebras closed under the taking of arbitrary products.
\end{comment}

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
Identities modeled by an algebra \ab{𝑨} are also modeled by every homomorphic image of
\ab{𝑨} and by every subalgebra of \ab{𝑨}.
\ifshort
We refer to these facts as \af{⊧-H-invar} and \af{⊧-S-invar}; their
definitions are similar to that of \af{⊧-I-invar}.
\else
These facts are formalized in \agda as follows.

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}{𝑩 : Algebra β ρᵇ}{p q : Term X} where
 ⊧-H-invar : 𝑨 ⊧ p ≈ q → 𝑩 IsHomImageOf 𝑨 → 𝑩 ⊧ p ≈ q
 ⊧-H-invar Apq (φh , φE) ρ = begin
       ⟦ p ⟧   ⟨$⟩               ρ    ≈˘⟨  cong ⟦ p ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ p ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈˘⟨  comm-hom-term φh p (φ⁻¹ ∘ ρ)        ⟩
   φ(  ⟦ p ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   cong ∣ φh ∣ (Apq (φ⁻¹ ∘ ρ))         ⟩
   φ(  ⟦ q ⟧ᴬ  ⟨$⟩ (     φ⁻¹  ∘  ρ))  ≈⟨   comm-hom-term φh q (φ⁻¹ ∘ ρ)        ⟩
       ⟦ q ⟧   ⟨$⟩ (φ ∘  φ⁻¹  ∘  ρ)   ≈⟨   cong ⟦ q ⟧(λ _ → InvIsInverseʳ φE)  ⟩
       ⟦ q ⟧   ⟨$⟩               ρ    ∎ where
   φ⁻¹ : 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ]
   φ⁻¹ = SurjInv ∣ φh ∣ φE
   private φ = (_⟨$⟩_ ∣ φh ∣)
   open Environment 𝑨  using () renaming ( ⟦_⟧ to ⟦_⟧ᴬ)
   open Environment 𝑩  using ( ⟦_⟧ ) ; open SetoidReasoning 𝔻[ 𝑩 ]

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
 ⊧-P-invar 𝒜pq a = begin
   ⟦ p ⟧₁               ⟨$⟩  a                ≈⟨   interp-prod 𝒜 p a            ⟩
   ( λ i → (⟦ 𝒜 i ⟧ p)  ⟨$⟩  λ x → (a x) i )  ≈⟨ (λ i → 𝒜pq i (λ x → (a x) i))  ⟩
   ( λ i → (⟦ 𝒜 i ⟧ q)  ⟨$⟩  λ x → (a x) i )  ≈˘⟨  interp-prod 𝒜 q a            ⟩
   ⟦ q ⟧₁               ⟨$⟩  a                ∎ where
  open Environment (⨅ 𝒜)  using () renaming ( ⟦_⟧ to ⟦_⟧₁ )
  open Environment        using ( ⟦_⟧ )
  open Setoid 𝔻[ ⨅ 𝒜 ]    using ( _≈_ )
  open SetoidReasoning 𝔻[ ⨅ 𝒜 ]

\end{code}
\fi

A \emph{variety} is a class of \ab{𝑆}-algebras that is closed under the taking of
homomorphic images, subalgebras, and arbitrary products.
%To represent varieties
%we define composable types representing \af H, \af S, and \af P and we define the type \af V to be the compos%ition of all three.
%If \ab{𝒦} is a class of \ab{𝑆}-algebras, then
If we define \af V \ab{𝒦} := \af H (\af S (\af P \ab{𝒦})), then \ab{𝒦} is a variety iff \af V \ab{𝒦} \aof{⊆} \ab{𝒦}.
%(The converse inclusion holds by virtue of the fact that \af V is a composition of closure operators.)
The class \af{V}~\ab{𝒦} is called the \defn{varietal closure} of \ab{𝒦}. Here is how we define \af{V} in type theory.
(The explicit universe level declarations that appear in the definition are needed for disambiguation.)

\begin{code}

module _  {α ρᵃ β ρᵇ γ ρᶜ δ ρᵈ : Level} where
 private a = α ⊔ ρᵃ ; b = β ⊔ ρᵇ
 V : ∀ ℓ ι → Pred(Algebra α ρᵃ) (a ⊔ ov ℓ) →  Pred(Algebra δ ρᵈ) _
 V ℓ ι 𝒦 = H{γ}{ρᶜ}{δ}{ρᵈ} (a ⊔ b ⊔ ℓ ⊔ ι) (S{β}{ρᵇ} (a ⊔ ℓ ⊔ ι) (P ℓ ι 𝒦))

\end{code}



The classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦}, and \af V \ab{𝒦} all satisfy the
same term identities.  We will only use a subset of the inclusions needed to prove this
assertion.\footnote{The others are included in the
\ualmodule{Setoid.Varieties.Preservation} module of the \agdaalgebras library.}
First, the closure operator \af H preserves the identities modeled by the
given class; this follows almost immediately from the invariance lemma
\af{⊧-H-invar}.

\begin{code}

module _  {X : Type χ}{𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 H-id1 : 𝒦 ⊫ p ≈ q → H{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 H-id1 σ 𝑩 (𝑨 , kA , BimgA) = ⊧-H-invar{p = p}{q} (σ 𝑨 kA) BimgA

\end{code}
The analogous preservation result for \af S is a consequence of the invariance lemma \af{⊧-S-invar}; the converse, which we call \af{S-id2}, has an equally straightforward proof.

\begin{code}

 S-id1 : 𝒦 ⊫ p ≈ q → S{β = α}{ρᵃ}ℓ 𝒦 ⊫ p ≈ q
 S-id1 σ 𝑩 (𝑨 , kA , B≤A) = ⊧-S-invar{p = p}{q} (σ 𝑨 kA) B≤A

 S-id2 : S ℓ 𝒦 ⊫ p ≈ q → 𝒦 ⊫ p ≈ q
 S-id2 Spq 𝑨 kA = Spq 𝑨 (𝑨 , (kA , ≤-reflexive))

\end{code}
The \agdaalgebras library includes analogous pairs of implications for \af P, \af H, and \af V, called \af{P-id1}, \af{P-id2}, \af{H-id1}, etc.
\ifshort
whose formalizations we suppress.
\else
In each case, we will only need the first implication, so we omit the others from this presentation.

\begin{code}

 P-id1 : ∀{ι} → 𝒦 ⊫ p ≈ q → P{β = α}{ρᵃ}ℓ ι 𝒦 ⊫ p ≈ q
 P-id1 σ 𝑨 (I , 𝒜 , kA , A≅⨅A) = ⊧-I-invar 𝑨 p q IH (≅-sym A≅⨅A) where
  IH : ⨅ 𝒜 ⊧ p ≈ q
  IH = ⊧-P-invar 𝒜 {p}{q} λ i → σ (𝒜 i) (kA i)

module _ {X : Type χ}{ι : Level}(ℓ : Level){𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)}{p q : Term X} where
 private aℓι = α ⊔ ρᵃ ⊔ ℓ ⊔ ι
 V-id1 : 𝒦 ⊫ p ≈ q → V ℓ ι 𝒦 ⊫ p ≈ q
 V-id1 σ 𝑩 (𝑨 , (⨅A , p⨅A , A≤⨅A) , BimgA) =
  H-id1{ℓ = aℓι}{𝒦 = S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)}{p = p}{q} spK⊧pq 𝑩 (𝑨 , (spA , BimgA)) where
   spA : 𝑨 ∈ S aℓι (P {β = α}{ρᵃ}ℓ ι 𝒦)
   spA = ⨅A , (p⨅A , A≤⨅A)
   spK⊧pq : S aℓι (P ℓ ι 𝒦) ⊫ p ≈ q
   spK⊧pq = S-id1{ℓ = aℓι}{p = p}{q} (P-id1{ℓ = ℓ} {𝒦 = 𝒦}{p = p}{q} σ)
\end{code}
\fi
%% -------------------------------------------------------------------------------------
\section{Free Algebras}
\label{free-algebras}
%% -----------------------------------------------------------------------------
\paragraph*{The absolutely free algebra}
The term algebra \af{𝑻} \ab X is the \emph{absolutely free} \ab{𝑆}-algebra over \ab X.
That is, for every \ab{𝑆}-algebra \ab{𝑨}, the following hold.
\begin{itemize}
\item Every function from \ab{X} to \af{𝕌[ \ab{𝑨} ]} lifts to a homomorphism from \af{𝑻} \ab{X} to \ab{𝑨}.
\item That homomorphism is unique.
\end{itemize}
Here we formalize the first of these properties by defining the lifting function \af{free-lift}
and its setoid analog \af{free-lift-func}, and then proving the latter is a homomorphism.%
\footnote{For the proof of uniqueness, see the \ualmodule{Setoid.Terms.Properties} module of the \agdaalgebras library.}

\begin{code}

module _ {X : Type χ}{𝑨 : Algebra α ρᵃ}(h : X → 𝕌[ 𝑨 ]) where
 free-lift : 𝕌[ 𝑻 X ] → 𝕌[ 𝑨 ]
 free-lift (ℊ x)       = h x
 free-lift (node f t)  = (f ̂ 𝑨) λ i → free-lift (t i)

 free-lift-func : 𝔻[ 𝑻 X ] ⟶ 𝔻[ 𝑨 ]
 free-lift-func ⟨$⟩ x = free-lift x
 cong free-lift-func = flcong where
  open Setoid 𝔻[ 𝑨 ] using ( _≈_ ) renaming ( reflexive to reflexiveᴬ )
  flcong : ∀ {s t} → s ≃ t → free-lift s ≈ free-lift t
  flcong (_≃_.rfl x) = reflexiveᴬ (≡.cong h x)
  flcong (_≃_.gnl x) = cong (Interp 𝑨) (≡.refl , λ i → flcong (x i))

 lift-hom : hom (𝑻 X) 𝑨
 lift-hom = free-lift-func ,
   mkhom λ{_}{a} → cong (Interp 𝑨) (≡.refl , λ i → (cong free-lift-func){a i} ≃-isRefl)

\end{code}

It turns out that the interpretation of a term \ab p in an environment \ab{η} is the same
as the free lift of \ab{η} evaluated at \ab p. We apply this fact a number of times in the sequel.

\begin{code}

module _  {X : Type χ} {𝑨 : Algebra α ρᵃ}   where
 open Setoid 𝔻[ 𝑨 ]  using ( _≈_ ; refl )
 open Environment 𝑨  using ( ⟦_⟧ )

 free-lift-interp : (η : X → 𝕌[ 𝑨 ])(p : Term X) → ⟦ p ⟧ ⟨$⟩ η ≈ (free-lift{𝑨 = 𝑨} η) p
 free-lift-interp η (ℊ x)       = refl
 free-lift-interp η (node f t)  = cong (Interp 𝑨) (≡.refl , (free-lift-interp η) ∘ t)
\end{code}
%% -----------------------------------------------------------------------------
\paragraph*{The relatively free algebra}
Given an arbitrary class \ab{𝒦} of \ab{𝑆}-algebras, we cannot expect that \T{X} belongs to \ab{𝒦}.
%, so we say \T{X} is free \emph{for} \ab{𝒦} (as opposed to free \emph{in} \ab{𝒦}).
Indeed, there may be no free algebra in \ab{𝒦}.
Nonetheless, it is always possible to construct an algebra that is free for \ab{𝒦} and belongs to the class \af{S} (\af{P} \ab{𝒦}).
Such an algebra is called a \defn{relatively free algebra over} \ab{X} (relative to \ab{𝒦}).
There are several informal approaches to defining this algebra.
We now describe the approach on which our formal construction is based and then we present the formalization.

Let \Free{X} denote the relatively free algebra over \ab{X}.  We represent
\Free{X} as the quotient
\T{X}~\af{/}~\afld{≈} where \ab x~\afld{≈}~\ab y if and only if
\ab h \ab x = \ab h \ab y for every homomorphism \ab h from \T{X} into a member of \ab{𝒦}.
%Then \Free{X} satisfies the identities in \af{Th} \ab{𝒦}.
%Indeed, for each pair \ab p \ab q : \Term{X}, if \ab{𝒦} \af{⊫} \ab p \af{≈} \ab
%q, then \ab p and \ab q belong to the same \afld{≈}-class, so \ab p and \ab q are
%identified in \Free{X}.
More precisely, if \ab{𝑨}~\aof{∈}~\ab{𝒦} and \ab h~\as{:}~\af{hom}~(\T{X})~\ab{𝑨}, then \ab h factors as \T{X} $\overset{\text{\ab h}}{\twoheadrightarrow}$ \af{HomIm}~\ab h $\overset{⊆}{↣}$ \ab{𝑨} and \T{X}~\af{/}~\af{ker}~\ab h ≅ \af{HomIm}~\ab h ≤ \ab{𝑨}; that is, \T{X}~\af{/}~\af{ker}~\ab h is (isomorphic to) an algebra in \af{S}~\ab{𝒦}. Letting
\afld{≈} := ⋂ \{\ab{θ}~\aof{∈}~\ab{Con}~\T{X}~∣~\T{X}~\af{/}~\ab{θ}~\aof{∈}~\af{S} \ab{𝒦}\},
observe that \Free{X} := \T{X}~\af{/}~\afld{≈} is a subdirect product of the algebras \{\T{X}~\af{/}~\af{ker}~\ab h\!\}
as \ab h ranges over all homomorphisms from \T{X} to algebras in \ab{𝒦}.  Thus, \Free{X} \af{∈}
\af{P} (\af{S} \ab{𝒦}) \aof{⊆} \af{S} (\af{P} \ab{𝒦}).
As we have seen,
%if \ab{𝑨}~\aof{∈}~\ab{𝒦}, then
every map \ab{ρ} : \ab X → \aof{𝕌[}~\ab{𝑨}~\aof{]}
extends uniquely to a homomorphism \ab h~\as{:}~\af{hom}~(\T{X})~\ab{𝑨} and \ab h
factors through the natural projection \T{X}~\as{→}~\Free{X} (since \afld{≈}~\aof{⊆}~\af{ker}~\ab h) yielding a unique homomorphism from \Free{X} to \ab{𝑨} extending ρ.
%≅ \af{HomIm}~\ab h ≤ \ab{𝑩}
%~\ab{θ}~\aof{∈}~\ab{Con}~\ab{𝑨} and

%\T{X}~\af{/}~\af{ker}~\ab h
%Moreover, \ab x~\afld{≈}~\ab y if and only if the pair (\ab x,~\ab y) belongs to all congruences \ab{θ}~\aof{∈}~\ab{Con}~\ab{𝑨} where \ab{𝑨} ranges over homomorphic images of algebras in \af{S}~\ab{𝒦}.


%Evidently \Free{X} is a subdirect product of all the algebras in \ab{𝒦}.

In \agda we construct \Free{X} as a homomorphic image of \T{X} in the following way.
First, given \ab X we define \ab{𝑪} as the product of pairs (\ab{𝑨}, \ab{ρ}) of
algebras \ab{𝑨}~\aof{∈}~\ab{𝒦} along with environments \ab{ρ}~\as{:}~\ab X~\as{→}~\aof{𝕌[}~\ab{𝑨}~\aof{]}.
To do so, we contrive an index type for the product;
%class \ab{𝒦} by letting the indices be the algebras in \ab{𝒦}. Actually,
each index is a triple (\ab{𝑨}, \ab p, \ab{ρ}) where \ab{𝑨} is an algebra, \ab p is proof of \ab{𝑨}~\aof{∈}~\ab{𝒦}, and \ab{ρ}~\as{:}~\ab X~\as{→}~\aof{𝕌[}~\ab{𝑨}~\aof{]} is an arbitrary environment.
%Using this indexing scheme, we construct \ab{𝑪}, as follows.
%The indexing type \ab{ℑ} %, the family of algebras \ab{𝔄},
%and the product \ab{𝑪} are defined as follows.

\begin{code}

module FreeAlgebra (𝒦 : Pred (Algebra α ρᵃ) ℓ) where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 ℑ : {χ : Level} → Type χ → Type (ι ⊔ χ)
 ℑ X = Σ[ 𝑨 ∈ Algebra α ρᵃ ] 𝑨 ∈ 𝒦 × (X → 𝕌[ 𝑨 ])

 𝑪 : {χ : Level} → Type χ → Algebra (ι ⊔ χ)(ι ⊔ χ)
 𝑪 X = ⨅ {I = ℑ X} ∣_∣

\end{code}
We then define \Free{X} to be the image of a homomorphism from \T{X} to \ab{𝑪} as follows.

\begin{code}

 homC : (X : Type χ) → hom (𝑻 X) (𝑪 X)
 homC X = ⨅-hom-co _ (λ i → lift-hom (snd ∥ i ∥))

 𝔽[_] : {χ : Level} → Type χ → Algebra (ov χ) (ι ⊔ χ)
 𝔽[ X ] = HomIm (homC X)

\end{code}

Observe that if the identity \ab{p} \af{≈} \ab q holds in all \ab{𝑨} \aof{∈} \ab{𝒦} (for all environments), then \ab p \af{≈} \ab q holds in \Free{X}; equivalently, the pair (\ab p , \ab q) belongs to the
kernel of the natural homomorphism from \T{X} onto \Free{X}.
This natural epimorphism %from \T{X} onto \Free{X} %(= \T{X}~\af{/}~\afld{≈})
is defined as follows.%
%and prove that its kernel is contained in the collection of identities modeled
%by \af{V} \ab{𝒦}.%(which we represent by \af{Th} (\af{V} \ab{𝒦})).
\ifshort%
\footnote{The \AgdaFunction{HomReduct} method of the \ar{IsEpi} record type extracts the \af{hom} part of an epimorphism.}
\fi

\begin{code}

module FreeHom {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ; ι = ov c ⊔ ℓ
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; homC )

 epiF[_] : (X : Type c) → epi (𝑻 X) 𝔽[ X ]
 epiF[ X ] = ∣ toHomIm (homC X) ∣ , record  { isHom = ∥ toHomIm (homC X) ∥
                                            ; isSurjective = toIm-surj ∣ homC X ∣ }

 homF[_] : (X : Type c) → hom (𝑻 X) 𝔽[ X ]
 homF[ X ] = IsEpi.HomReduct ∥ epiF[ X ] ∥

\end{code}

Before formalizing the HSP theorem in the next section, we need to prove the following important property of the relatively free algebra:
%(relative to \ab{𝒦} and satisfying the identities in \af{Th}~\ab{𝒦}),
For every algebra \ab{𝑨}, if \ab{𝑨}~\af{⊨}~\ab{Th}~(\af{V}~\ab{𝒦}),
then there exists an epimorphism from \Free{A} onto \ab{𝑨}, where \ab{A} denotes the carrier of \ab{𝑨}.

\begin{code}

module _ {𝑨 : Algebra (α ⊔ ρᵃ ⊔ ℓ)(α ⊔ ρᵃ ⊔ ℓ)}{𝒦 : Pred(Algebra α ρᵃ)(α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c
 open FreeAlgebra 𝒦 using ( 𝔽[_] ; 𝑪 )
 open Setoid 𝔻[ 𝑨 ] using ( refl ; sym ; trans ) renaming ( Carrier to A ; _≈_ to _≈ᴬ_ )

 F-ModTh-epi : 𝑨 ∈ Mod (Th 𝒦) → epi 𝔽[ A ]  𝑨
 F-ModTh-epi A∈ModThK = φ , isEpi where

  φ : 𝔻[ 𝔽[ A ] ] ⟶ 𝔻[ 𝑨 ]
  _⟨$⟩_ φ            = free-lift{𝑨 = 𝑨} id
  cong φ {p} {q} pq  = Goal
   where
   lift-pq : (p , q) ∈ Th 𝒦
   lift-pq 𝑩 x ρ = begin
    ⟦ p ⟧ ⟨$⟩ ρ    ≈⟨ free-lift-interp {𝑨 = 𝑩} ρ p  ⟩
    free-lift ρ p  ≈⟨ pq (𝑩 , x , ρ)                ⟩
    free-lift ρ q  ≈˘⟨ free-lift-interp{𝑨 = 𝑩} ρ q  ⟩
    ⟦ q ⟧ ⟨$⟩ ρ    ∎
     where open SetoidReasoning 𝔻[ 𝑩 ] ; open Environment 𝑩 using ( ⟦_⟧ )

   Goal : free-lift id p ≈ᴬ free-lift id q
   Goal = begin
    free-lift id p  ≈˘⟨ free-lift-interp {𝑨 = 𝑨} id p   ⟩
    ⟦ p ⟧ ⟨$⟩ id    ≈⟨ A∈ModThK {p = p} {q} lift-pq id  ⟩
    ⟦ q ⟧ ⟨$⟩ id    ≈⟨ free-lift-interp {𝑨 = 𝑨} id q    ⟩
    free-lift id q  ∎
     where open SetoidReasoning 𝔻[ 𝑨 ] ; open Environment 𝑨 using ( ⟦_⟧ )

  isEpi : IsEpi 𝔽[ A ] 𝑨 φ
  isEpi = record { isHom = mkhom refl ; isSurjective = eq (ℊ _) refl }

 F-ModThV-epi : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ]  𝑨
 F-ModThV-epi A∈ModThVK = F-ModTh-epi λ {p}{q} → Goal {p}{q}
  where
  Goal : 𝑨 ∈ Mod (Th 𝒦)
  Goal {p}{q} x ρ = A∈ModThVK{p}{q} (V-id1 ℓ {p = p}{q} x) ρ
\end{code}
\ifshort\else

\noindent Actually, we will need the following lifted version of this result.

\begin{code}

 F-ModTh-epi-lift : 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → epi 𝔽[ A ] (Lift-Alg 𝑨 ι ι)
 F-ModTh-epi-lift A∈ModThK = ∘-epi (F-ModThV-epi λ {p q} → A∈ModThK{p = p}{q} ) ToLift-epi
\end{code}
\fi


%% -------------------------------------------------------------------------------------

\section{Birkhoff's Variety Theorem}

Let \ab{𝒦} be a class of algebras and recall that \ab{𝒦} is a \emph{variety} provided
it is closed under homomorphisms, subalgebras and products; equivalently,
\af{V} \ab{𝒦} ⊆ \ab{𝒦}.
(Observe that \ab{𝒦} ⊆ \af{V} \ab{𝒦} holds for all \ab{𝒦} since \af{V} is a closure operator.)
We call \ab{𝒦} an \emph{equational class} if it is the class of all models of some set of identities.

Birkhoff's variety theorem, also known as the HSP theorem, asserts that \ab{𝒦}
is an equational class if and only if it is a variety.  In this section, we present the
statement and proof of this theorem---first in a style similar to
what one finds in textbooks (e.g.,~\cite[Theorem 4.41]{Bergman:2012}),
and then formally in the language of \mltt.
%--------------------------------------
\paragraph*{Informal proof}

%--------------------------------------
\noindent (⇒) \textit{Every equational class is a variety}. Indeed, suppose \ab{𝒦} is an equational
class axiomatized by term identities \ab{ℰ}; that is, \ab{𝑨} ∈ \ab{𝒦} iff
\ab{𝑨} \af{⊨} \ab{ℰ}. Since the classes \af H \ab{𝒦}, \af S \ab{𝒦}, \af P \ab{𝒦} and
\ab{𝒦} all satisfy the same set of equations, we have \af{V} \ab{𝒦} \af{⊫} \ab p
\af{≈} \ab q for all (\ab p , \ab q) \af{∈} \ab{ℰ}, so \af{V} \ab{𝒦} ⊆ \ab{𝒦}.

\medskip

%--------------------------------------
\noindent (⇐) \textit{Every variety is an equational class}.\footnote{The proof we present here is based on~\cite[Theorem 4.41]{Bergman:2012}.}
Let \ab{𝒦} be an arbitrary variety.  We will describe a set of equations that axiomatizes
\ab{𝒦}.  A natural choice is to take \af{Th} \ab{𝒦} and try to prove that \ab{𝒦} \aof{=} \af{Mod} (\af{Th} \ab{𝒦}). Clearly, \ab{𝒦}~\aof{⊆}~\af{Mod}~(\af{Th}~\ab{𝒦}).  To prove the converse inclusion, let \ab{𝑨}~\af{∈}~\af{Mod}~(\af{Th}~\ab{𝒦}). It suffices to find an algebra \ab{𝑭} \af{∈} \af{S} (\af{P} \ab{𝒦}) such that
\ab{𝑨} is a homomorphic image of \ab{𝑭}, as this will show that \ab{𝑨} \af{∈}
\af{H} (\af{S} (\af{P} \ab{𝒦})) = \ab{𝒦}.

Let \ab{X} be such that there exists a surjective environment
\ab{ρ} : \ab{X} \as{→} \af{𝕌[~\ab{𝑨}~]}.\footnote{Informally, this is done by assuming \ab{X} has cardinality at least max(|~\af{𝕌[~\ab{𝑨}~]}~|, ω). Later we will see how to construct an \ab{X} with the required property in type theory.}
By the \af{lift-hom} lemma, there is an epimorphism \ab{h} : \T{X} \as{→} \aof{𝕌[~\ab{𝑨}~]}
that extends \ab{ρ}.
Put \aof{𝔽[~\ab{X}~]}~:=~\T{X}/\afld{≈} and let \ab{g} : \T{X} \as{→} \aof{𝔽[~\ab{X}~]}
be the natural epimorphism with kernel \afld{≈}. We claim \af{ker} \ab g \af{⊆}
\af{ker} \ab h. If the claim is true, then there is a map \ab{f} : \aof{𝔽[~\ab{X}~]} \as{→} \ab{𝑨}
such that \ab f \af{∘} \ab g = \ab h, and since \ab h is surjective so is \ab f. Therefore, \ab{𝑨}
\af{∈} \af{𝖧} (\af{𝔽} \ab X) \aof{⊆} \af{Mod} (\af{Th} \ab{𝒦}) completing the proof.

It remains to prove the claim \af{ker} \ab g \af{⊆} \af{ker} \ab h. Let \ab u, \ab v be terms
and assume \ab g \ab u = \ab g \ab v. Since \T{X} is generated by \ab X, there are terms
\ab p, \ab q such that \ab u = \af{⟦~\T{X}~⟧}~\ab p and v = \af{⟦~\T{X}~⟧}~\ab q.
%\footnote{Recall, \af{⟦~\ab{𝑨}~⟧} \ab t denotes the interpretation of the term
%\ab t in the algebra \ab{𝑨}.}
Therefore,
\ifshort
\af{⟦~\Free{X}~⟧} \ab p = \ab g (\af{⟦~\T{X}~⟧} \ab p) = \ab g \ab u = \ab g \ab v =
\ab g (\af{⟦~\T{X}~⟧} \ab q) = \af{⟦~\Free{X}~⟧} \ab q,
\else
\begin{center}
\af{⟦~\Free{X}~⟧} \ab p = \ab g (\af{⟦~\T{X}~⟧} \ab p) = \ab g \ab u = \ab g \ab v =
\ab g (\af{⟦~\T{X}~⟧} \ab q) = \af{⟦~\Free{X}~⟧} \ab q,
\end{center}
\fi
so \ab{𝒦}~\af{⊫}~\ab p~\af{≈}~\ab q; thus, (\ab p , \ab q) \af{∈} \af{Th}
\ab{𝒦}. Since \ab{𝑨} \af{∈} \af{Mod} (\af{Th} \ab{𝒦}), we obtain \ab{𝑨}~\af{⊧}~\ab p~\af{≈}~\ab q, which implies
that \ab h \ab u = (\af{⟦~\ab{𝑨}~⟧} \ab p) \aofld{⟨\$⟩} \ab{ρ} = (\af{⟦~\ab{𝑨}~⟧} \ab q)
\aofld{⟨\$⟩} \ab{ρ} = \ab h \ab v, as desired.

\paragraph*{Formal proof}
%We now show how to express and prove the twin assertions that
%(⇐) every equational class is a variety and (⇒) every variety is an equational class.
%% -----------------------------------------------------------------------------
(⇒) \textit{Every equational class is a variety}.
We need an arbitrary equational class, which we obtain by starting with an arbitrary
collection \ab{ℰ} of equations and then defining \ab{𝒦} = \af{Mod} \ab{ℰ}, the class
axiomatized by \ab{ℰ}. We prove that \ab{𝒦} is a variety by showing that
\ab{𝒦} = \af{V}~\ab{𝒦}. The inclusion \ab{𝒦}~\aof{⊆}~\af V~\ab{𝒦}, which holds for all
classes \ab{𝒦}, is called the \defn{expansive} property of \af{V}.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)) where
 V-expa : 𝒦 ⊆ V ℓ (ov (α ⊔ ρᵃ ⊔ ℓ)) 𝒦
 V-expa {x = 𝑨}kA = 𝑨 , (𝑨 , (⊤ , (λ _ → 𝑨), (λ _ → kA), Goal), ≤-reflexive), IdHomImage
  where
  open Setoid 𝔻[ 𝑨 ]            using ( refl )
  open Setoid 𝔻[ ⨅ (λ _ → 𝑨) ]  using () renaming ( refl to refl⨅ )
  to⨅    : 𝔻[ 𝑨 ]            ⟶ 𝔻[ ⨅ (λ _ → 𝑨) ]
  to⨅    = record { f = λ x _ → x   ; cong = λ xy _ → xy }
  from⨅  : 𝔻[ ⨅ (λ _ → 𝑨) ]  ⟶ 𝔻[ 𝑨 ]
  from⨅  = record { f = λ x → x tt  ; cong = λ xy → xy tt }
  Goal   : 𝑨 ≅ ⨅ (λ x → 𝑨)
  Goal   = mkiso (to⨅ , mkhom refl⨅) (from⨅ , mkhom refl) (λ _ _ → refl) (λ _ → refl)

\end{code}
Observe how \ab{𝑨} is expressed as (isomorphic to) a product with just one factor (itself), that is, the product
\af{⨅} (\as{λ} \ab x \as{→} \ab{𝑨}) indexed over the one-element type \af{⊤}.

For the inclusion \af V \ab{𝒦} \aof{⊆} \ab{𝒦},
%requires the assumption that \ab{𝒦} is an equational class. R
recall lemma \af{V-id1} which asserts that \ab{𝒦} \aof{⊫} \ab p \aof{≈} \ab q implies
\af{V}~\ab{ℓ}~\ab{ι}~\ab{𝒦}~\aof{⊫}~\ab p~\aof{≈}~\ab q; whence, if \ab{𝒦} is an equational
class, then \af V \ab{𝒦} \aof{⊆} \ab{𝒦}, as we now confirm.

\begin{code}

module _ {ℓ : Level}{X : Type ℓ}{ℰ : {Y : Type ℓ} → Pred (Term Y × Term Y) (ov ℓ)} where
 private 𝒦 = Mod{α = ℓ}{ℓ}{X} ℰ     -- an arbitrary equational class

 EqCl⇒Var : V ℓ (ov ℓ) 𝒦 ⊆ 𝒦
 EqCl⇒Var {𝑨} vA {p} {q} pℰq ρ = V-id1 ℓ {𝒦} {p} {q} (λ _ x τ → x pℰq τ) 𝑨 vA ρ

\end{code}
By \af{V-expa} and \af{Eqcl⇒Var}, every equational class is a variety.
%% -----------------------------------------------------------------------------

\bigskip

\noindent (⇐) \textit{Every variety is an equational class}.
To fix an arbitrary variety, start with an arbitrary class
\ab{𝒦} of \ab{𝑆}-algebras and take the \emph{varietal closure}, \af{V} \ab{𝒦}.
We prove that \af{V} \ab{𝒦} is precisely the collection of
algebras that model \af{Th} (\af{V} \ab{𝒦}); that is, \af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})).
The inclusion \af{V} \ab{𝒦} \aof{⊆} \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) is a
consequence of the fact that \af{Mod} \af{Th} is a closure operator.

\begin{code}

module _ (𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)){X : Type (α ⊔ ρᵃ ⊔ ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 ModTh-closure : V{β = β}{ρᵇ}{γ}{ρᶜ}{δ}{ρᵈ} ℓ ι 𝒦 ⊆ Mod{X = X} (Th (V ℓ ι 𝒦))
 ModTh-closure {x = 𝑨} vA {p} {q} x ρ = x 𝑨 vA ρ

\end{code}
Our proof of the inclusion \af{Mod} (\af{Th} (\af V \ab{𝒦})) \aof{⊆} \af{V} \ab{𝒦} is carried out in two steps.

\begin{enumerate}
\item \label{item:1} Prove \aof{𝔽[ \ab{X} ]} \af{≤} \ab{𝑪} \ab X.
\item \label{item:2} Prove that every algebra in \af{Mod} (\af{Th} (\af{V}~\ab{𝒦})) is a homomorphic image of
\aof{𝔽[ \ab{X} ]}.
\end{enumerate}

\noindent From \ref{item:1} we have \aof{𝔽[ \ab{X} ]} \af{∈} \af{S} (\af{P} \ab{𝒦})), since \ab{𝑪}~\ab X is a product of algebras in \ab{𝒦}. From this and \ref{item:2} will follow \af{Mod}~(\af{Th}~(\af{V}~\ab{𝒦})) ⊆ \af{H}~(\af{S}~(\af{P}~\ab{𝒦})) (= \af{V} \ab{𝒦}), as desired.

\begin{itemize}
\item \noindent \ref{item:1}. To prove \Free{X} \af{≤} \ab{𝑪} \ab X, we construct a homomorphism from
\Free{X} to \ab{𝑪}~\ab X and then show it is injective,
so \Free{X} is (isomorphic to) a subalgebra of \af{𝑪}~\ab X.
%\footnote{The function \af{mon→≤} in the proof of \af{F≤C} merely extracts a subalgebra witness from a monomorphism.}

%\T{X} to \ab{𝑪} whose kernel contains the kernel \afld{≈} of \aof{homF[}~\ab X~\aof{]} (the natural hom from \T{X} onto \Free{X}).

\begin{code}

 open FreeHom {ℓ = ℓ}{𝒦}
 open FreeAlgebra 𝒦 using (homC ;  𝔽[_] ; 𝑪 )
 homFC : hom 𝔽[ X ] (𝑪 X)
 homFC = fromHomIm (homC X)

 monFC : mon 𝔽[ X ] (𝑪 X)
 monFC = ∣ homFC ∣ , record { isHom = ∥ homFC ∥
                            ; isInjective =  λ {x}{y}→ fromIm-inj ∣ homC X ∣ {x}{y}   }
 F≤C : 𝔽[ X ] ≤ 𝑪 X
 F≤C = mon→≤ monFC

 open FreeAlgebra 𝒦 using ( ℑ )

 SPF : 𝔽[ X ] ∈ S ι (P ℓ ι 𝒦)
 SPF = 𝑪 X , ((ℑ X) , (∣_∣ , ((λ i → fst ∥ i ∥) , ≅-refl))) ,  F≤C
\end{code}
\end{itemize}

\begin{itemize}
\item \ref{item:2}. Every algebra in \af{Mod} (\af{Th} (\af{V}
\ab{𝒦})) is a homomorphic image of \af{𝔽[~\ab{X}~]}. Indeed,
\begin{code}

module _ {𝒦 : Pred(Algebra α ρᵃ) (α ⊔ ρᵃ ⊔ ov ℓ)} where
 private c = α ⊔ ρᵃ ⊔ ℓ ; ι = ov c

 Var⇒EqCl : ∀ 𝑨 → 𝑨 ∈ Mod (Th (V ℓ ι 𝒦)) → 𝑨 ∈ V ℓ ι 𝒦
 Var⇒EqCl 𝑨 ModThA = 𝔽[ 𝕌[ 𝑨 ] ] , (SPF{ℓ = ℓ} 𝒦 , Aim)
  where
  open FreeAlgebra 𝒦 using ( 𝔽[_] )
  epiFlA : epi 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι)
  epiFlA = F-ModTh-epi-lift{ℓ = ℓ} λ {p q} → ModThA{p = p}{q}

  φ : Lift-Alg 𝑨 ι ι IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  φ = epi→ontohom 𝔽[ 𝕌[ 𝑨 ] ] (Lift-Alg 𝑨 ι ι) epiFlA

  Aim : 𝑨 IsHomImageOf 𝔽[ 𝕌[ 𝑨 ] ]
  Aim = ∘-hom ∣ φ ∣(from Lift-≅), ∘-IsSurjective _ _ ∥ φ ∥(fromIsSurjective(Lift-≅{𝑨 = 𝑨}))

\end{code}
By \af{ModTh-closure} and \af{Var⇒EqCl}, we have
\af{V} \ab{𝒦} = \af{Mod} (\af{Th} (\af{V} \ab{𝒦})) for every class \ab{𝒦} of \ab{𝑆}-algebras.
Thus, every variety is an equational class.
\end{itemize}

This completes the formal proof of Birkhoff's variety theorem. \hfill \qedsymbol

%% -----------------------------------------------------------------------------
\section{Discussion}\label{sec:discuss}
How do we differ from the classical, set-theoretic approach? Most noticeable is
our avoidance of all \emph{size} issues. By using universe levels and level
polymorphism, we always make sure we are in a \emph{large enough} universe.
So we can easily talk about ``all algebras such that \ldots'' because these are
always taken from a bounded (but arbitrary) universe.

Our use of setoids introduces nothing new: all the equivalence relations we
use were already present in the classical proofs. The only ``new'' material is
that we have to prove that functions respect those equivalences.

Our first attempt to formalize Birkhoff's theorem was not sufficiently
careful in its handling of variable symbols \ab X. Specifically, this
type was unconstrained; it is meant to represent the informal notion of a ``sufficiently large'' collection of variable symbols. Consequently, we postulated surjections from \ab X onto the
domains of all algebras in the class under consideration.
%The quantifiers were in the wrong order!
But then, given a signature \ab{𝑆} and a one-element \ab{𝑆}-algebra \ab{𝑨},
by choosing \ab X to be the empty type \ab{⊥}, our surjectivity postulate gives a map from \ab{⊥} onto the singleton domain of \ab{𝑨}. (For details, see the \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/ContraX.lagda}{\am{Demos.ContraX}} module which constructs the counterexample in \agda.)

\begin{comment}
The inconsistency in our first effort to formalize Birkhoff's theorem was due to careless handling of the type \ab X of variable symbols.  Specifically, we had allowed \ab X to be any type whatever. Informally, \ab X is a ``sufficiently large'' collection of variable symbols and, in our first formal statement of Birkhoff's theorem, we made the following assumption: (h1) there exist surjections from \ab X to the domain of every algebra in the class under consideration.  Informally, this isn't a problem if we view (h1) as implicitly requiring that \ab X be a type for which such surjections could possibly exist.  Technically, however, by exploiting the freedom to choose \ab X arbitrarily, a contradiction can be contrived.  Specifically, if we take \ab X to be the empty type and take the one-element \ab{𝑆}-algebra. By (h1), there is a surjective map from the empty type to a nonempty type, which is clearly a contradiction.
(See the \href{https://github.com/ualib/agda-algebras/blob/master/src/Demos/ContraX.lagda}{\am{Demos.ContraX}} module in the \agdaalgebrasrepo repository for the formal counterexample.)
\end{comment}

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
Finally, in~\cite{Abel:2021}, Abel gives a new formal proof of the soundness and completeness
theorem for multi-sorted algebraic structures.

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













\begin{comment}

%The \defn{relatively free algebra over} \ab{X} (relative to
%\ab{𝒦}) is defined to be the quotient \Free{X} := \T{X}~\af{/}~\afld{≈}.


is the least equivalence relation on \T{X} such that
on such that (1) ∀ (\ab p , \ab q) \af{∈} \af{Th} \ab{𝒦}, ∀ \ab{ρ} : \ab X \as{→} \Term{X}, \af{⟦~\ab p~⟧} \afld{⟨\$⟩} \ab{ρ} \afld{≈} \af{⟦~\ab q~⟧} \afld{⟨\$⟩} \ab{ρ}, and (2) \afld{≈} ∈ \af{Con} \T{X}.  Alternatively, }
\footnote{More precisely, the equivalence relation on \T{X} generated by \ab{ℰ} is the least equivalence relation on \T{X} such that
on such that (1) ∀ (\ab p , \ab q) \af{∈} \af{Th} \ab{𝒦}, ∀ \ab{ρ} : \ab X \as{→} \Term{X}, \af{⟦~\ab p~⟧} \afld{⟨\$⟩} \ab{ρ} \afld{≈} \af{⟦~\ab q~⟧} \afld{⟨\$⟩} \ab{ρ}, and (2) \afld{≈} ∈ \af{Con} \T{X}.  Alternatively, }
proceeds by taking the quotient of \T{X} modulo the congruence relation \afld{≈} := \af{⋂}\{\ab{θ} \af{∈} \af{Con} (\T{X}) : \T{X} \af{/} \ab{θ} \af{∈} \af{S}
\ab{𝒦}\}.\footnote{\af{Con} (\T{X}) denotes the congruences of \T{X}.}$^,$\footnote{Alternatively,
we could let \ab{ℰ} = \af{Th} \ab{𝒦} and take \afld{≈} to be the least equivalence relation
on T(X) such that (1) ∀ (\ab p , \ab q) \af{∈} \af{Th} \ab{𝒦}, ∀ \ab{ρ} : \ab X \as{→} \Term{X}, \af{⟦~\ab p~⟧} \afld{⟨\$⟩} \ab{ρ} \afld{≈} \af{⟦~\ab q~⟧} \afld{⟨\$⟩} \ab{ρ}, and (2) \afld{≈} ∈ \af{Con} \T{X}}
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
\end{comment}
%
