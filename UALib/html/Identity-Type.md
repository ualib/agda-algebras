<pre class="Agda">

<a id="15" class="Symbol">{-#</a> <a id="19" class="Keyword">OPTIONS</a> <a id="27" class="Pragma">--without-K</a> <a id="39" class="Pragma">--exact-split</a> <a id="53" class="Pragma">--safe</a> <a id="60" class="Symbol">#-}</a>

<a id="65" class="Keyword">module</a> <a id="72" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="86" class="Keyword">where</a>

<a id="93" class="Keyword">open</a> <a id="98" class="Keyword">import</a> <a id="105" href="Universes.html" class="Module">Universes</a>

<a id="116" class="Keyword">data</a> <a id="_≡_"></a><a id="121" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="125" class="Symbol">{</a><a id="126" href="Identity-Type.html#126" class="Bound">𝓤</a><a id="127" class="Symbol">}</a> <a id="129" class="Symbol">{</a><a id="130" href="Identity-Type.html#130" class="Bound">X</a> <a id="132" class="Symbol">:</a> <a id="134" href="Identity-Type.html#126" class="Bound">𝓤</a> <a id="136" href="Universes.html#403" class="Function Operator">̇</a> <a id="138" class="Symbol">}</a> <a id="140" class="Symbol">:</a> <a id="142" href="Identity-Type.html#130" class="Bound">X</a> <a id="144" class="Symbol">→</a> <a id="146" href="Identity-Type.html#130" class="Bound">X</a> <a id="148" class="Symbol">→</a> <a id="150" href="Identity-Type.html#126" class="Bound">𝓤</a> <a id="152" href="Universes.html#403" class="Function Operator">̇</a> <a id="154" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="162" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="167" class="Symbol">:</a> <a id="169" class="Symbol">{</a><a id="170" href="Identity-Type.html#170" class="Bound">x</a> <a id="172" class="Symbol">:</a> <a id="174" href="Identity-Type.html#130" class="Bound">X</a><a id="175" class="Symbol">}</a> <a id="177" class="Symbol">→</a> <a id="179" href="Identity-Type.html#170" class="Bound">x</a> <a id="181" href="Identity-Type.html#121" class="Datatype Operator">≡</a> <a id="183" href="Identity-Type.html#170" class="Bound">x</a>

</pre>
