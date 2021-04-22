---
layout: default
title : Sigma-Type.md
---

<pre class="Agda">

<a id="15" class="Symbol">{-#</a> <a id="19" class="Keyword">OPTIONS</a> <a id="27" class="Pragma">--without-K</a> <a id="39" class="Pragma">--exact-split</a> <a id="53" class="Pragma">--safe</a> <a id="60" class="Symbol">#-}</a>

<a id="65" class="Keyword">module</a> <a id="72" href="Sigma-Type.html" class="Module">Sigma-Type</a> <a id="83" class="Keyword">where</a>

<a id="90" class="Keyword">open</a> <a id="95" class="Keyword">import</a> <a id="102" href="Universes.html" class="Module">Universes</a>

<a id="113" class="Keyword">record</a> <a id="Σ"></a><a id="120" href="Sigma-Type.html#120" class="Record">Σ</a> <a id="122" class="Symbol">{</a><a id="123" href="Sigma-Type.html#123" class="Bound">𝓤</a> <a id="125" href="Sigma-Type.html#125" class="Bound">𝓥</a><a id="126" class="Symbol">}</a> <a id="128" class="Symbol">{</a><a id="129" href="Sigma-Type.html#129" class="Bound">X</a> <a id="131" class="Symbol">:</a> <a id="133" href="Sigma-Type.html#123" class="Bound">𝓤</a> <a id="135" href="Universes.html#403" class="Function Operator">̇</a> <a id="137" class="Symbol">}</a> <a id="139" class="Symbol">(</a><a id="140" href="Sigma-Type.html#140" class="Bound">Y</a> <a id="142" class="Symbol">:</a> <a id="144" href="Sigma-Type.html#129" class="Bound">X</a> <a id="146" class="Symbol">→</a> <a id="148" href="Sigma-Type.html#125" class="Bound">𝓥</a> <a id="150" href="Universes.html#403" class="Function Operator">̇</a> <a id="152" class="Symbol">)</a> <a id="154" class="Symbol">:</a> <a id="156" href="Sigma-Type.html#123" class="Bound">𝓤</a> <a id="158" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="160" href="Sigma-Type.html#125" class="Bound">𝓥</a> <a id="162" href="Universes.html#403" class="Function Operator">̇</a>  <a id="165" class="Keyword">where</a>
  <a id="173" class="Keyword">constructor</a>
   <a id="_,_"></a><a id="188" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a>
  <a id="194" class="Keyword">field</a>
   <a id="Σ.pr₁"></a><a id="203" href="Sigma-Type.html#203" class="Field">pr₁</a> <a id="207" class="Symbol">:</a> <a id="209" href="Sigma-Type.html#129" class="Bound">X</a>
   <a id="Σ.pr₂"></a><a id="214" href="Sigma-Type.html#214" class="Field">pr₂</a> <a id="218" class="Symbol">:</a> <a id="220" href="Sigma-Type.html#140" class="Bound">Y</a> <a id="222" href="Sigma-Type.html#203" class="Field">pr₁</a>

<a id="227" class="Keyword">infixr</a> <a id="234" class="Number">50</a> <a id="237" href="Sigma-Type.html#188" class="InductiveConstructor Operator">_,_</a>

</pre>
