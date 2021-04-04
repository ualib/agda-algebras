---
layout: default
title : Natural-Numbers-Type
---

<pre class="Agda">

<a id="15" class="Symbol">{-#</a> <a id="19" class="Keyword">OPTIONS</a> <a id="27" class="Pragma">--without-K</a> <a id="39" class="Pragma">--exact-split</a> <a id="53" class="Pragma">--safe</a> <a id="60" class="Symbol">#-}</a>

<a id="65" class="Keyword">module</a> <a id="72" href="Natural-Numbers-Type.html" class="Module">Natural-Numbers-Type</a> <a id="93" class="Keyword">where</a>

<a id="100" class="Keyword">data</a> <a id="ℕ"></a><a id="105" href="Natural-Numbers-Type.html#105" class="Datatype">ℕ</a> <a id="107" class="Symbol">:</a> <a id="109" class="PrimitiveType">Set₀</a>  <a id="115" class="Keyword">where</a>
 <a id="ℕ.zero"></a><a id="122" href="Natural-Numbers-Type.html#122" class="InductiveConstructor">zero</a> <a id="127" class="Symbol">:</a> <a id="129" href="Natural-Numbers-Type.html#105" class="Datatype">ℕ</a>
 <a id="ℕ.succ"></a><a id="132" href="Natural-Numbers-Type.html#132" class="InductiveConstructor">succ</a> <a id="137" class="Symbol">:</a> <a id="139" href="Natural-Numbers-Type.html#105" class="Datatype">ℕ</a> <a id="141" class="Symbol">→</a> <a id="143" href="Natural-Numbers-Type.html#105" class="Datatype">ℕ</a>

<a id="146" class="Symbol">{-#</a> <a id="150" class="Keyword">BUILTIN</a> <a id="158" class="Keyword">NATURAL</a> <a id="166" href="Natural-Numbers-Type.html#105" class="Datatype">ℕ</a> <a id="168" class="Symbol">#-}</a>

</pre>
