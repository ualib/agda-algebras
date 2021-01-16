<pre class="Agda">

<a id="15" class="Symbol">{-#</a> <a id="19" class="Keyword">OPTIONS</a> <a id="27" class="Pragma">--without-K</a> <a id="39" class="Pragma">--exact-split</a> <a id="53" class="Pragma">--safe</a> <a id="60" class="Symbol">#-}</a>

<a id="65" class="Keyword">module</a> <a id="72" href="Universes.html" class="Module">Universes</a> <a id="82" class="Keyword">where</a>

<a id="89" class="Keyword">open</a> <a id="94" class="Keyword">import</a> <a id="101" href="Agda.Primitive.html" class="Module">Agda.Primitive</a> <a id="116" class="Keyword">public</a>
  <a id="125" class="Keyword">using</a> <a id="131" class="Symbol">(</a><a id="132" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="135" class="Symbol">)</a>
  <a id="139" class="Keyword">renaming</a> <a id="148" class="Symbol">(</a><a id="149" href="Agda.Primitive.html#590" class="Primitive">lzero</a> <a id="155" class="Symbol">to</a> <a id="Primitive.lzero"></a><a id="158" href="Universes.html#158" class="Primitive">𝓤₀</a>
          <a id="171" class="Symbol">;</a> <a id="173" href="Agda.Primitive.html#606" class="Primitive">lsuc</a> <a id="178" class="Symbol">to</a> <a id="Primitive.lsuc"></a><a id="181" href="Universes.html#181" class="Primitive">_⁺</a>
          <a id="194" class="Symbol">;</a> <a id="196" href="Agda.Primitive.html#423" class="Postulate">Level</a> <a id="202" class="Symbol">to</a> <a id="Primitive.Level"></a><a id="205" href="Universes.html#205" class="Postulate">Universe</a>
          <a id="224" class="Symbol">;</a> <a id="226" href="Agda.Primitive.html#787" class="Primitive">Setω</a> <a id="231" class="Symbol">to</a> <a id="Primitive.Setω"></a><a id="234" href="Universes.html#234" class="Primitive">𝓤ω</a>
          <a id="247" class="Symbol">)</a>

<a id="250" class="Keyword">variable</a>
 <a id="260" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="262" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="264" href="Universes.html#264" class="Generalizable">𝓦</a> <a id="266" href="Universes.html#266" class="Generalizable">𝓣</a> <a id="268" href="Universes.html#268" class="Generalizable">𝓤&#39;</a> <a id="271" href="Universes.html#271" class="Generalizable">𝓥&#39;</a> <a id="274" href="Universes.html#274" class="Generalizable">𝓦&#39;</a> <a id="277" href="Universes.html#277" class="Generalizable">𝓣&#39;</a> <a id="280" class="Symbol">:</a> <a id="282" href="Universes.html#205" class="Postulate">Universe</a>

</pre>

The following should be the only use of the Agda keyword 'Set' in this
development:

<pre class="Agda">

<a id="_̇"></a><a id="403" href="Universes.html#403" class="Function Operator">_̇</a> <a id="406" class="Symbol">:</a> <a id="408" class="Symbol">(</a><a id="409" href="Universes.html#409" class="Bound">𝓤</a> <a id="411" class="Symbol">:</a> <a id="413" href="Universes.html#205" class="Postulate">Universe</a><a id="421" class="Symbol">)</a> <a id="423" class="Symbol">→</a> <a id="425" class="Symbol">_</a>
<a id="427" href="Universes.html#427" class="Bound">𝓤</a> <a id="429" href="Universes.html#403" class="Function Operator">̇</a> <a id="431" class="Symbol">=</a> <a id="433" class="PrimitiveType">Set</a> <a id="437" href="Universes.html#427" class="Bound">𝓤</a>

<a id="𝓤₁"></a><a id="440" href="Universes.html#440" class="Function">𝓤₁</a> <a id="443" class="Symbol">=</a> <a id="445" href="Universes.html#158" class="Primitive">𝓤₀</a> <a id="448" href="Universes.html#181" class="Primitive Operator">⁺</a>
<a id="𝓤₂"></a><a id="450" href="Universes.html#450" class="Function">𝓤₂</a> <a id="453" class="Symbol">=</a> <a id="455" href="Universes.html#440" class="Function">𝓤₁</a> <a id="458" href="Universes.html#181" class="Primitive Operator">⁺</a>

<a id="_⁺⁺"></a><a id="461" href="Universes.html#461" class="Function Operator">_⁺⁺</a> <a id="465" class="Symbol">:</a> <a id="467" href="Universes.html#205" class="Postulate">Universe</a> <a id="476" class="Symbol">→</a> <a id="478" href="Universes.html#205" class="Postulate">Universe</a>
<a id="487" href="Universes.html#487" class="Bound">𝓤</a> <a id="489" href="Universes.html#461" class="Function Operator">⁺⁺</a> <a id="492" class="Symbol">=</a> <a id="494" href="Universes.html#487" class="Bound">𝓤</a> <a id="496" href="Universes.html#181" class="Primitive Operator">⁺</a> <a id="498" href="Universes.html#181" class="Primitive Operator">⁺</a>

</pre>

This is mainly to avoid naming implicit arguments:

<pre class="Agda">

<a id="universe-of"></a><a id="579" href="Universes.html#579" class="Function">universe-of</a> <a id="591" class="Symbol">:</a> <a id="593" class="Symbol">(</a><a id="594" href="Universes.html#594" class="Bound">X</a> <a id="596" class="Symbol">:</a> <a id="598" href="Universes.html#260" class="Generalizable">𝓤</a> <a id="600" href="Universes.html#403" class="Function Operator">̇</a> <a id="602" class="Symbol">)</a> <a id="604" class="Symbol">→</a> <a id="606" href="Universes.html#205" class="Postulate">Universe</a>
<a id="615" href="Universes.html#579" class="Function">universe-of</a> <a id="627" class="Symbol">{</a><a id="628" href="Universes.html#628" class="Bound">𝓤</a><a id="629" class="Symbol">}</a> <a id="631" href="Universes.html#631" class="Bound">X</a> <a id="633" class="Symbol">=</a> <a id="635" href="Universes.html#628" class="Bound">𝓤</a>

</pre>

precedences:

<pre class="Agda">

<a id="678" class="Keyword">infix</a>  <a id="685" class="Number">1</a> <a id="687" href="Universes.html#403" class="Function Operator">_̇</a>

</pre>
