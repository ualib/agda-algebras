---
layout: default
title : UALib.Terms.Basic module (The Agda Universal Algebra Library)
date : 2021-01-14
author: William DeMeo
---

### <a id="basic-definitions">Basic definitions</a>

This section presents the [UALib.Terms.Basic][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="302" class="Symbol">{-#</a> <a id="306" class="Keyword">OPTIONS</a> <a id="314" class="Pragma">--without-K</a> <a id="326" class="Pragma">--exact-split</a> <a id="340" class="Pragma">--safe</a> <a id="347" class="Symbol">#-}</a>

<a id="352" class="Keyword">open</a> <a id="357" class="Keyword">import</a> <a id="364" href="UALib.Algebras.html" class="Module">UALib.Algebras</a> <a id="379" class="Keyword">using</a> <a id="385" class="Symbol">(</a><a id="386" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a><a id="395" class="Symbol">;</a> <a id="397" href="universes.html#613" class="Generalizable">𝓞</a><a id="398" class="Symbol">;</a> <a id="400" href="universes.html#617" class="Generalizable">𝓥</a><a id="401" class="Symbol">;</a> <a id="403" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a><a id="410" class="Symbol">;</a> <a id="412" href="UALib.Algebras.Lifts.html#4574" class="Function Operator">_↠_</a><a id="415" class="Symbol">)</a>
<a id="417" class="Keyword">open</a> <a id="422" class="Keyword">import</a> <a id="429" href="UALib.Prelude.Preliminaries.html" class="Module">UALib.Prelude.Preliminaries</a> <a id="457" class="Keyword">using</a> <a id="463" class="Symbol">(</a><a id="464" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="478" class="Symbol">;</a> <a id="480" href="universes.html#551" class="Postulate">Universe</a><a id="488" class="Symbol">;</a> <a id="490" href="universes.html#758" class="Function Operator">_̇</a><a id="492" class="Symbol">)</a>


<a id="496" class="Keyword">module</a> <a id="503" href="UALib.Terms.Basic.html" class="Module">UALib.Terms.Basic</a>
 <a id="522" class="Symbol">{</a><a id="523" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="525" class="Symbol">:</a> <a id="527" href="UALib.Algebras.Signatures.html#802" class="Function">Signature</a> <a id="537" href="universes.html#613" class="Generalizable">𝓞</a> <a id="539" href="universes.html#617" class="Generalizable">𝓥</a><a id="540" class="Symbol">}{</a><a id="542" href="UALib.Terms.Basic.html#542" class="Bound">gfe</a> <a id="546" class="Symbol">:</a> <a id="548" href="MGS-Subsingleton-Theorems.html#3468" class="Function">global-dfunext</a><a id="562" class="Symbol">}</a>
 <a id="565" class="Symbol">{</a><a id="566" href="UALib.Terms.Basic.html#566" class="Bound">𝕏</a> <a id="568" class="Symbol">:</a> <a id="570" class="Symbol">{</a><a id="571" href="UALib.Terms.Basic.html#571" class="Bound">𝓤</a> <a id="573" href="UALib.Terms.Basic.html#573" class="Bound">𝓧</a> <a id="575" class="Symbol">:</a> <a id="577" href="universes.html#551" class="Postulate">Universe</a><a id="585" class="Symbol">}{</a><a id="587" href="UALib.Terms.Basic.html#587" class="Bound">X</a> <a id="589" class="Symbol">:</a> <a id="591" href="UALib.Terms.Basic.html#573" class="Bound">𝓧</a> <a id="593" href="universes.html#758" class="Function Operator">̇</a> <a id="595" class="Symbol">}(</a><a id="597" href="UALib.Terms.Basic.html#597" class="Bound">𝑨</a> <a id="599" class="Symbol">:</a> <a id="601" href="UALib.Algebras.Algebras.html#1471" class="Function">Algebra</a> <a id="609" href="UALib.Terms.Basic.html#571" class="Bound">𝓤</a> <a id="611" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a><a id="612" class="Symbol">)</a> <a id="614" class="Symbol">→</a> <a id="616" href="UALib.Terms.Basic.html#587" class="Bound">X</a> <a id="618" href="UALib.Algebras.Lifts.html#4574" class="Function Operator">↠</a> <a id="620" href="UALib.Terms.Basic.html#597" class="Bound">𝑨</a><a id="621" class="Symbol">}</a>
 <a id="624" class="Keyword">where</a>


<a id="632" class="Keyword">open</a> <a id="637" class="Keyword">import</a> <a id="644" href="UALib.Homomorphisms.HomomorphicImages.html" class="Module">UALib.Homomorphisms.HomomorphicImages</a><a id="681" class="Symbol">{</a><a id="682" class="Argument">𝑆</a> <a id="684" class="Symbol">=</a> <a id="686" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a><a id="687" class="Symbol">}{</a><a id="689" href="UALib.Terms.Basic.html#542" class="Bound">gfe</a><a id="692" class="Symbol">}</a> <a id="694" class="Keyword">hiding</a> <a id="701" class="Symbol">(</a>Universe<a id="710" class="Symbol">;</a> _̇<a id="714" class="Symbol">)</a> <a id="716" class="Keyword">public</a>

</pre>

#### The inductive type of terms

<pre class="Agda">

<a id="784" class="Keyword">data</a> <a id="Term"></a><a id="789" href="UALib.Terms.Basic.html#789" class="Datatype">Term</a> <a id="794" class="Symbol">{</a><a id="795" href="UALib.Terms.Basic.html#795" class="Bound">𝓧</a> <a id="797" class="Symbol">:</a> <a id="799" href="universes.html#551" class="Postulate">Universe</a><a id="807" class="Symbol">}{</a><a id="809" href="UALib.Terms.Basic.html#809" class="Bound">X</a> <a id="811" class="Symbol">:</a> <a id="813" href="UALib.Terms.Basic.html#795" class="Bound">𝓧</a> <a id="815" href="universes.html#758" class="Function Operator">̇</a><a id="816" class="Symbol">}</a> <a id="818" class="Symbol">:</a> <a id="820" href="UALib.Terms.Basic.html#537" class="Bound">𝓞</a> <a id="822" href="Agda.Primitive.html#636" class="Function Operator">⊔</a> <a id="824" href="UALib.Terms.Basic.html#539" class="Bound">𝓥</a> <a id="826" href="Agda.Primitive.html#636" class="Function Operator">⊔</a> <a id="828" href="UALib.Terms.Basic.html#795" class="Bound">𝓧</a> <a id="830" href="universes.html#527" class="Function Operator">⁺</a> <a id="832" href="universes.html#758" class="Function Operator">̇</a>  <a id="835" class="Keyword">where</a>
  <a id="Term.generator"></a><a id="843" href="UALib.Terms.Basic.html#843" class="InductiveConstructor">generator</a> <a id="853" class="Symbol">:</a> <a id="855" href="UALib.Terms.Basic.html#809" class="Bound">X</a> <a id="857" class="Symbol">→</a> <a id="859" href="UALib.Terms.Basic.html#789" class="Datatype">Term</a><a id="863" class="Symbol">{</a><a id="864" href="UALib.Terms.Basic.html#795" class="Bound">𝓧</a><a id="865" class="Symbol">}{</a><a id="867" href="UALib.Terms.Basic.html#809" class="Bound">X</a><a id="868" class="Symbol">}</a>
  <a id="Term.node"></a><a id="872" href="UALib.Terms.Basic.html#872" class="InductiveConstructor">node</a> <a id="877" class="Symbol">:</a> <a id="879" class="Symbol">(</a><a id="880" href="UALib.Terms.Basic.html#880" class="Bound">f</a> <a id="882" class="Symbol">:</a> <a id="884" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a> <a id="886" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="888" href="UALib.Prelude.Preliminaries.html#7503" class="Function Operator">∣</a><a id="889" class="Symbol">)(</a><a id="891" href="UALib.Terms.Basic.html#891" class="Bound">args</a> <a id="896" class="Symbol">:</a> <a id="898" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="900" href="UALib.Terms.Basic.html#523" class="Bound">𝑆</a> <a id="902" href="UALib.Prelude.Preliminaries.html#7581" class="Function Operator">∥</a> <a id="904" href="UALib.Terms.Basic.html#880" class="Bound">f</a> <a id="906" class="Symbol">→</a> <a id="908" href="UALib.Terms.Basic.html#789" class="Datatype">Term</a><a id="912" class="Symbol">{</a><a id="913" href="UALib.Terms.Basic.html#795" class="Bound">𝓧</a><a id="914" class="Symbol">}{</a><a id="916" href="UALib.Terms.Basic.html#809" class="Bound">X</a><a id="917" class="Symbol">})</a> <a id="920" class="Symbol">→</a> <a id="922" href="UALib.Terms.Basic.html#789" class="Datatype">Term</a>

<a id="928" class="Keyword">open</a> <a id="933" href="UALib.Terms.Basic.html#789" class="Module">Term</a>

</pre>

--------------------------------------

[↑ UALib.Terms](UALib.Terms.html)
<span style="float:right;">[UALib.Terms.Free →](UALib.Terms.Free.html)</span>

{% include UALib.Links.md %}
