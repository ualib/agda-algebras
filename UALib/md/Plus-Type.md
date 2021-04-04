---
layout: default
title : Plus-Type module
---

<pre class="Agda">

<a id="15" class="Symbol">{-#</a> <a id="19" class="Keyword">OPTIONS</a> <a id="27" class="Pragma">--without-K</a> <a id="39" class="Pragma">--exact-split</a> <a id="53" class="Pragma">--safe</a> <a id="60" class="Symbol">#-}</a>

<a id="65" class="Keyword">module</a> <a id="72" href="Plus-Type.html" class="Module">Plus-Type</a> <a id="82" class="Keyword">where</a>

<a id="89" class="Keyword">open</a> <a id="94" class="Keyword">import</a> <a id="101" href="Universes.html" class="Module">Universes</a> <a id="111" class="Keyword">public</a>

<a id="119" class="Keyword">data</a> <a id="_+_"></a><a id="124" href="Plus-Type.html#124" class="Datatype Operator">_+_</a> <a id="128" class="Symbol">{</a><a id="129" href="Plus-Type.html#129" class="Bound">𝓤</a> <a id="131" href="Plus-Type.html#131" class="Bound">𝓥</a><a id="132" class="Symbol">}</a> <a id="134" class="Symbol">(</a><a id="135" href="Plus-Type.html#135" class="Bound">X</a> <a id="137" class="Symbol">:</a> <a id="139" href="Plus-Type.html#129" class="Bound">𝓤</a> <a id="141" href="Universes.html#403" class="Function Operator">̇</a> <a id="143" class="Symbol">)</a> <a id="145" class="Symbol">(</a><a id="146" href="Plus-Type.html#146" class="Bound">Y</a> <a id="148" class="Symbol">:</a> <a id="150" href="Plus-Type.html#131" class="Bound">𝓥</a> <a id="152" href="Universes.html#403" class="Function Operator">̇</a> <a id="154" class="Symbol">)</a> <a id="156" class="Symbol">:</a> <a id="158" href="Plus-Type.html#129" class="Bound">𝓤</a> <a id="160" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="162" href="Plus-Type.html#131" class="Bound">𝓥</a> <a id="164" href="Universes.html#403" class="Function Operator">̇</a>  <a id="167" class="Keyword">where</a>
 <a id="_+_.inl"></a><a id="174" href="Plus-Type.html#174" class="InductiveConstructor">inl</a> <a id="178" class="Symbol">:</a> <a id="180" href="Plus-Type.html#135" class="Bound">X</a> <a id="182" class="Symbol">→</a> <a id="184" href="Plus-Type.html#135" class="Bound">X</a> <a id="186" href="Plus-Type.html#124" class="Datatype Operator">+</a> <a id="188" href="Plus-Type.html#146" class="Bound">Y</a>
 <a id="_+_.inr"></a><a id="191" href="Plus-Type.html#191" class="InductiveConstructor">inr</a> <a id="195" class="Symbol">:</a> <a id="197" href="Plus-Type.html#146" class="Bound">Y</a> <a id="199" class="Symbol">→</a> <a id="201" href="Plus-Type.html#135" class="Bound">X</a> <a id="203" href="Plus-Type.html#124" class="Datatype Operator">+</a> <a id="205" href="Plus-Type.html#146" class="Bound">Y</a>

</pre>
