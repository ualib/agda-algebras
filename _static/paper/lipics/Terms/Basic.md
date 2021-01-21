---
layout: default
title : UALib.Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic definitions</a>

This section presents the [UALib.Terms.Basic][] module of the [Agda Universal Algebra Library][].

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaSymbol{\{-\#}\AgdaSpace{}%
\AgdaKeyword{OPTIONS}\AgdaSpace{}%
\AgdaPragma{--without-K}\AgdaSpace{}%
\AgdaPragma{--exact-split}\AgdaSpace{}%
\AgdaPragma{--safe}\AgdaSpace{}%
\AgdaSymbol{\#-\}}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{UALib.Algebras}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{Signature}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaGeneralizable{𝓞}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaGeneralizable{𝓥}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaFunction{Algebra}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}↠\AgdaUnderscore{}}}\AgdaSymbol{)}\<%
\\
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{UALib.Prelude.Preliminaries}\AgdaSpace{}%
\AgdaKeyword{using}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaFunction{global-dfunext}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaPostulate{Universe}\AgdaSymbol{;}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{\AgdaUnderscore{}̇}}\AgdaSymbol{)}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{module}\AgdaSpace{}%
\AgdaModule{UALib.Terms.Basic}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[1]\AgdaSymbol{\{}\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaFunction{Signature}\AgdaSpace{}%
\AgdaGeneralizable{𝓞}\AgdaSpace{}%
\AgdaGeneralizable{𝓥}\AgdaSymbol{\}\{}\AgdaBound{gfe}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaFunction{global-dfunext}\AgdaSymbol{\}}\<%
\\
%
\>[1]\AgdaSymbol{\{}\AgdaBound{𝕏}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{𝓤}\AgdaSpace{}%
\AgdaBound{𝓧}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{Universe}\AgdaSymbol{\}\{}\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{𝓧}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSpace{}%
\AgdaSymbol{\}(}\AgdaBound{𝑨}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaFunction{Algebra}\AgdaSpace{}%
\AgdaBound{𝓤}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{↠}}\AgdaSpace{}%
\AgdaBound{𝑨}\AgdaSymbol{\}}\<%
\\
%
\>[1]\AgdaKeyword{where}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaKeyword{import}\AgdaSpace{}%
\AgdaModule{UALib.Homomorphisms.HomomorphicImages}\AgdaSymbol{\{}\AgdaArgument{𝑆}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSymbol{\}\{}\AgdaBound{gfe}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaKeyword{hiding}\AgdaSpace{}%
\AgdaSymbol{(}Universe\AgdaSymbol{;} \AgdaUnderscore{}̇\AgdaSymbol{)}\AgdaSpace{}%
\AgdaKeyword{public}\<%
\\
\>[0]\<%
\end{code}

-----------------------------------------------

#### <a id="the-inductive-type-of-terms">The inductive type of terms</a>

We define a type called `Term` which, not surprisingly, represents the type of terms. The type `X :  𝒰 ̇` represents an arbitrary collection of variable symbols.

\begin{code}%
\>[0]\<%
\\
\>[0]\AgdaKeyword{data}\AgdaSpace{}%
\AgdaDatatype{Term}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaBound{𝓧}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaPostulate{Universe}\AgdaSymbol{\}\{}\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{𝓧}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}\AgdaSymbol{\}}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{𝓞}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⊔}}\AgdaSpace{}%
\AgdaBound{𝓥}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⊔}}\AgdaSpace{}%
\AgdaBound{𝓧}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⁺}}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{̇}}%
\>[51]\AgdaKeyword{where}\<%
\\
\>[0][@{}l@{\AgdaIndent{0}}]%
\>[2]\AgdaInductiveConstructor{generator}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{X}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Term}\AgdaSymbol{\{}\AgdaBound{𝓧}\AgdaSymbol{\}\{}\AgdaBound{X}\AgdaSymbol{\}}\<%
\\
%
\>[2]\AgdaInductiveConstructor{node}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∣}}\AgdaSymbol{)(}\AgdaBound{args}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{𝑆}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{∥}}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Term}\AgdaSymbol{\{}\AgdaBound{𝓧}\AgdaSymbol{\}\{}\AgdaBound{X}\AgdaSymbol{\})}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaDatatype{Term}\<%
\\
%
\\[\AgdaEmptyExtraSkip]%
\>[0]\AgdaKeyword{open}\AgdaSpace{}%
\AgdaModule{Term}\<%
\\
\>[0]\<%
\end{code}

--------------------------------------

[↑ UALib.Terms](UALib.Terms.html)
<span style="float:right;">[UALib.Terms.Free →](UALib.Terms.Free.html)</span>

{% include UALib.Links.md %}
