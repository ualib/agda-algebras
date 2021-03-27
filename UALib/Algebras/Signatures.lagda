---
layout: default
title : Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

\AgdaTarget{Op, π, Signature, monoid-op, monoid-sig, e, Algebras.Signatures}

\subsection{Operations and Signatures}\label{operations-and-signatures}

This section presents the \AgdaModule{Algebras.Signatures} module of the \href{https://ualib.gitlab.io}{Agda Universal Algebra Library}.


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}
open import Universes using (𝓤₀)
module Algebras.Signatures where
open import Relations.Truncation public
\end{code}

\subsubsection{Operation type}\label{operation-type}

We define the type of \textit{operations}, as follows.

\begin{code}
Op : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Op I A = (I → A) → A
\end{code}

The type \AgdaFunction{Op} encodes the arity of an operation as an arbitrary type \AgdaBound{I}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaBound{𝓥}\AgdaFunction{̇}, which gives us a very general way to represent an operation as a function type with domain \AgdaBound{I}\AgdaSpace{}\AgdaSymbol{→}\AgdaSpace{}\AgdaBound{A} (the type of ``tuples'') and codomain \AgdaBound{A}. For example, the \AgdaBound{I}-\textit{ary projection operations} on \AgdaBound{A} are represented as inhabitants of the type \AgdaFunction{Op}\AgdaSpace{}\AgdaBound{I}\AgdaSpace{}\AgdaBound{A} as follows.

\begin{code}
π : {I : 𝓥 ̇ } {A : 𝓤 ̇ } → I → Op I A
π i x = x i
\end{code}


\subsubsection{Signature type}\label{signature-type}

We define the signature of an algebraic structure in Agda like this.


\begin{code}
Signature : (𝓞 𝓥 : Universe) → (𝓞 ⊔ 𝓥) ⁺ ̇
Signature 𝓞 𝓥 = Σ F ꞉ 𝓞 ̇ , (F → 𝓥 ̇)
\end{code}

As mentioned in the \AgdaModule{Relations.Continuous} module, \AgdaBound{𝓞} will always denote the universe of \textit{operation symbol} types, while \AgdaBound{𝓥} denotes the universe of \textit{arity} types.

In the \AgdaModule{Overture} module we defined special syntax for the first and second projections---namely, \AgdaFunction{∣\_∣} and \AgdaFunction{∥\_∥}, resp. Consequently, if \AgdaBound{𝑆}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaFunction{Signature}\AgdaSpace{}\AgdaBound{𝓞}\AgdaBound{𝓥} is a signature, then
\AgdaOperator{\AgdaFunction{∣}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}
denotes the set of operation symbols, and 
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∥}}
denotes the arity function. If \AgdaBound{𝑓}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}
is an operation symbol in the signature \AgdaBound{𝑆}, then
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{𝑓} is the arity of \AgdaBound{𝑓}.

\subsubsection{Example}\label{sec:example}

Here is how we could define the signature for monoids as a member of the type \AgdaFunction{Signature}\AgdaSpace{}\AgdaBound{𝓞}\AgdaSpace{}\AgdaBound{𝓥}.

\begin{code}
data monoid-op {𝓞 : Universe} : 𝓞 ̇ where
 e : monoid-op
 · : monoid-op

open import MGS-MLTT using (𝟘; 𝟚)

monoid-sig : Signature 𝓞 𝓤₀
monoid-sig = monoid-op , λ { e → 𝟘; · → 𝟚 }
\end{code}

As expected, the signature for a monoid consists of two operation symbols, \AgdaInductiveConstructor{e} and \AgdaInductiveConstructor{·}, and a function
\AgdaSymbol{λ}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaSpace{}%
\AgdaInductiveConstructor{e}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaFunction{𝟘}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaInductiveConstructor{·}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaFunction{𝟚}\AgdaSpace{}%
\AgdaSymbol{\}}
which maps \AgdaInductiveConstructor{e} to the empty type \AgdaFunction{𝟘} (since \AgdaInductiveConstructor{e} is the nullary identity) and maps \AgdaInductiveConstructor{·} to the two element type \AgdaFunction{𝟚} (since \AgdaInductiveConstructor{·} is binary).

% -------------------------------------

% [↑ Algebras](Algebras.html)
% <span style="float:right;">[Algebras.Algebras →](Algebras.Algebras.html)</span>


% {% include UALib.Links.md %}

