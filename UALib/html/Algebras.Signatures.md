---
layout: default
title : Algebras.Signatures module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

\AgdaTarget{Op, π, Signature, monoid-op, monoid-sig, e, Algebras.Signatures}

\subsection{Operations and Signatures}\label{operations-and-signatures}

This section presents the \AgdaModule{Algebras.Signatures} module of the \href{https://ualib.gitlab.io}{Agda Universal Algebra Library}.


<pre class="Agda">
<a id="437" class="Symbol">{-#</a> <a id="441" class="Keyword">OPTIONS</a> <a id="449" class="Pragma">--without-K</a> <a id="461" class="Pragma">--exact-split</a> <a id="475" class="Pragma">--safe</a> <a id="482" class="Symbol">#-}</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="Universes.html" class="Module">Universes</a> <a id="508" class="Keyword">using</a> <a id="514" class="Symbol">(</a><a id="515" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a><a id="517" class="Symbol">)</a>
<a id="519" class="Keyword">module</a> <a id="526" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="546" class="Keyword">where</a>
<a id="552" class="Keyword">open</a> <a id="557" class="Keyword">import</a> <a id="564" href="Relations.Truncation.html" class="Module">Relations.Truncation</a> <a id="585" class="Keyword">public</a>
</pre>

\subsubsection{Operation type}\label{operation-type}

We define the type of \textit{operations}, as follows.

<pre class="Agda">
<a id="Op"></a><a id="727" href="Algebras.Signatures.html#727" class="Function">Op</a> <a id="730" class="Symbol">:</a> <a id="732" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="734" href="Universes.html#403" class="Function Operator">̇</a> <a id="736" class="Symbol">→</a> <a id="738" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="740" href="Universes.html#403" class="Function Operator">̇</a> <a id="742" class="Symbol">→</a> <a id="744" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="746" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="748" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="750" href="Universes.html#403" class="Function Operator">̇</a>
<a id="752" href="Algebras.Signatures.html#727" class="Function">Op</a> <a id="755" href="Algebras.Signatures.html#755" class="Bound">I</a> <a id="757" href="Algebras.Signatures.html#757" class="Bound">A</a> <a id="759" class="Symbol">=</a> <a id="761" class="Symbol">(</a><a id="762" href="Algebras.Signatures.html#755" class="Bound">I</a> <a id="764" class="Symbol">→</a> <a id="766" href="Algebras.Signatures.html#757" class="Bound">A</a><a id="767" class="Symbol">)</a> <a id="769" class="Symbol">→</a> <a id="771" href="Algebras.Signatures.html#757" class="Bound">A</a>
</pre>

The type \AgdaFunction{Op} encodes the arity of an operation as an arbitrary type \AgdaBound{I}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaBound{𝓥}\AgdaFunction{̇}, which gives us a very general way to represent an operation as a function type with domain \AgdaBound{I}\AgdaSpace{}\AgdaSymbol{→}\AgdaSpace{}\AgdaBound{A} (the type of ``tuples'') and codomain \AgdaBound{A}. For example, the \AgdaBound{I}-\textit{ary projection operations} on \AgdaBound{A} are represented as inhabitants of the type \AgdaFunction{Op}\AgdaSpace{}\AgdaBound{I}\AgdaSpace{}\AgdaBound{A} as follows.

<pre class="Agda">
<a id="π"></a><a id="1378" href="Algebras.Signatures.html#1378" class="Function">π</a> <a id="1380" class="Symbol">:</a> <a id="1382" class="Symbol">{</a><a id="1383" href="Algebras.Signatures.html#1383" class="Bound">I</a> <a id="1385" class="Symbol">:</a> <a id="1387" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="1389" href="Universes.html#403" class="Function Operator">̇</a> <a id="1391" class="Symbol">}</a> <a id="1393" class="Symbol">{</a><a id="1394" href="Algebras.Signatures.html#1394" class="Bound">A</a> <a id="1396" class="Symbol">:</a> <a id="1398" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="1400" href="Universes.html#403" class="Function Operator">̇</a> <a id="1402" class="Symbol">}</a> <a id="1404" class="Symbol">→</a> <a id="1406" href="Algebras.Signatures.html#1383" class="Bound">I</a> <a id="1408" class="Symbol">→</a> <a id="1410" href="Algebras.Signatures.html#727" class="Function">Op</a> <a id="1413" href="Algebras.Signatures.html#1383" class="Bound">I</a> <a id="1415" href="Algebras.Signatures.html#1394" class="Bound">A</a>
<a id="1417" href="Algebras.Signatures.html#1378" class="Function">π</a> <a id="1419" href="Algebras.Signatures.html#1419" class="Bound">i</a> <a id="1421" href="Algebras.Signatures.html#1421" class="Bound">x</a> <a id="1423" class="Symbol">=</a> <a id="1425" href="Algebras.Signatures.html#1421" class="Bound">x</a> <a id="1427" href="Algebras.Signatures.html#1419" class="Bound">i</a>
</pre>


\subsubsection{Signature type}\label{signature-type}

We define the signature of an algebraic structure in Agda like this.


<pre class="Agda">
<a id="Signature"></a><a id="1580" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="1590" class="Symbol">:</a> <a id="1592" class="Symbol">(</a><a id="1593" href="Algebras.Signatures.html#1593" class="Bound">𝓞</a> <a id="1595" href="Algebras.Signatures.html#1595" class="Bound">𝓥</a> <a id="1597" class="Symbol">:</a> <a id="1599" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1607" class="Symbol">)</a> <a id="1609" class="Symbol">→</a> <a id="1611" class="Symbol">(</a><a id="1612" href="Algebras.Signatures.html#1593" class="Bound">𝓞</a> <a id="1614" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1616" href="Algebras.Signatures.html#1595" class="Bound">𝓥</a><a id="1617" class="Symbol">)</a> <a id="1619" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a> <a id="1621" href="Universes.html#403" class="Function Operator">̇</a>
<a id="1623" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="1633" href="Algebras.Signatures.html#1633" class="Bound">𝓞</a> <a id="1635" href="Algebras.Signatures.html#1635" class="Bound">𝓥</a> <a id="1637" class="Symbol">=</a> <a id="1639" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="1641" href="Algebras.Signatures.html#1641" class="Bound">F</a> <a id="1643" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="1645" href="Algebras.Signatures.html#1633" class="Bound">𝓞</a> <a id="1647" href="Universes.html#403" class="Function Operator">̇</a> <a id="1649" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="1651" class="Symbol">(</a><a id="1652" href="Algebras.Signatures.html#1641" class="Bound">F</a> <a id="1654" class="Symbol">→</a> <a id="1656" href="Algebras.Signatures.html#1635" class="Bound">𝓥</a> <a id="1658" href="Universes.html#403" class="Function Operator">̇</a><a id="1659" class="Symbol">)</a>
</pre>

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

<pre class="Agda">
<a id="3070" class="Keyword">data</a> <a id="monoid-op"></a><a id="3075" href="Algebras.Signatures.html#3075" class="Datatype">monoid-op</a> <a id="3085" class="Symbol">{</a><a id="3086" href="Algebras.Signatures.html#3086" class="Bound">𝓞</a> <a id="3088" class="Symbol">:</a> <a id="3090" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3098" class="Symbol">}</a> <a id="3100" class="Symbol">:</a> <a id="3102" href="Algebras.Signatures.html#3086" class="Bound">𝓞</a> <a id="3104" href="Universes.html#403" class="Function Operator">̇</a> <a id="3106" class="Keyword">where</a>
 <a id="monoid-op.e"></a><a id="3113" href="Algebras.Signatures.html#3113" class="InductiveConstructor">e</a> <a id="3115" class="Symbol">:</a> <a id="3117" href="Algebras.Signatures.html#3075" class="Datatype">monoid-op</a>
 <a id="monoid-op.·"></a><a id="3128" href="Algebras.Signatures.html#3128" class="InductiveConstructor">·</a> <a id="3130" class="Symbol">:</a> <a id="3132" href="Algebras.Signatures.html#3075" class="Datatype">monoid-op</a>

<a id="3143" class="Keyword">open</a> <a id="3148" class="Keyword">import</a> <a id="3155" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3164" class="Keyword">using</a> <a id="3170" class="Symbol">(</a><a id="3171" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="3172" class="Symbol">;</a> <a id="3174" href="MGS-MLTT.html#2482" class="Function">𝟚</a><a id="3175" class="Symbol">)</a>

<a id="monoid-sig"></a><a id="3178" href="Algebras.Signatures.html#3178" class="Function">monoid-sig</a> <a id="3189" class="Symbol">:</a> <a id="3191" href="Algebras.Signatures.html#1580" class="Function">Signature</a> <a id="3201" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="3203" href="Agda.Primitive.html#590" class="Primitive">𝓤₀</a>
<a id="3206" href="Algebras.Signatures.html#3178" class="Function">monoid-sig</a> <a id="3217" class="Symbol">=</a> <a id="3219" href="Algebras.Signatures.html#3075" class="Datatype">monoid-op</a> <a id="3229" href="Overture.Preliminaries.html#13001" class="InductiveConstructor Operator">,</a> <a id="3231" class="Symbol">λ</a> <a id="3233" class="Symbol">{</a> <a id="3235" href="Algebras.Signatures.html#3113" class="InductiveConstructor">e</a> <a id="3237" class="Symbol">→</a> <a id="3239" href="MGS-MLTT.html#712" class="Function">𝟘</a><a id="3240" class="Symbol">;</a> <a id="3242" href="Algebras.Signatures.html#3128" class="InductiveConstructor">·</a> <a id="3244" class="Symbol">→</a> <a id="3246" href="MGS-MLTT.html#2482" class="Function">𝟚</a> <a id="3248" class="Symbol">}</a>
</pre>

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

