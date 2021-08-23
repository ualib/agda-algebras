---
layout: default
title : Complexity.Basic module (The Agda Universal Algebra Library)
date : 2021-07-13
author: [agda-algebras development team][]
---

### <a id="complexity-theory">Complexity Theory</a>

<pre class="Agda">

<a id="223" class="Symbol">{-#</a> <a id="227" class="Keyword">OPTIONS</a> <a id="235" class="Pragma">--without-K</a> <a id="247" class="Pragma">--exact-split</a> <a id="261" class="Pragma">--safe</a> <a id="268" class="Symbol">#-}</a>

<a id="273" class="Keyword">module</a> <a id="280" href="Complexity.Basic.html" class="Module">Complexity.Basic</a> <a id="297" class="Keyword">where</a>


</pre>

#### <a id="words">Words</a>

Let 𝑇ₙ be a totally ordered set of size 𝑛.  Let 𝐴 be a set (the alphabet).
We can model the set 𝑊ₙ, of *words* (strings of letters from 𝐴) of length 𝑛
by the type 𝑇ₙ → 𝐴 of functions from 𝑇ₙ to 𝐴.

The set of all (finite length) words is then

\[ W = ⋃[n ∈ ℕ] Wₙ \]

The *length* of a word 𝑥 is given by the function `size x`, which will be defined below.

An *algorithm* is a computer program with infinite memory (i.e., a Turing machine).

A function 𝑓 : 𝑊 → 𝑊 is *computable in polynomial time* if there exist an
algorithm and numbers 𝑐, 𝑑 ∈ ℕ such that for each word 𝑥 ∈ 𝑊 the algorithm
stops in at most (size 𝑥) 𝑐 + 𝑑 steps and computes 𝑓 𝑥.

At first we will simplify by assuming 𝑇ₙ is `Fin n`.


--------------------------------

<br>
<br>

[↑ Complexity](Complexity.html)
<span style="float:right;">[Complexity.CSP →](Complexity.CSP.html)</span>

{% include UALib.Links.md %}

[agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team


