---
layout: default
title : UALib.Prelude.Equality module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---

### <a id="equality">Equality</a>

This section describes the [UALib.Prelude.Equality][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="291" class="Symbol">{-#</a> <a id="295" class="Keyword">OPTIONS</a> <a id="303" class="Pragma">--without-K</a> <a id="315" class="Pragma">--exact-split</a> <a id="329" class="Pragma">--safe</a> <a id="336" class="Symbol">#-}</a>

<a id="341" class="Keyword">module</a> <a id="348" href="Prelude.Equality.html" class="Module">Prelude.Equality</a> <a id="365" class="Keyword">where</a>

<a id="372" class="Keyword">open</a> <a id="377" class="Keyword">import</a> <a id="384" href="Prelude.Preliminaries.html" class="Module">Prelude.Preliminaries</a> <a id="406" class="Keyword">public</a>

</pre>

#### <a id="definitional-equality">Definitional equality</a>

The type referred to as "reflexivity" or "refl" is a very basic but important one. It represents [definitional equality](https://ncatlab.org/nlab/show/equality#definitional_equality).

The `refl` type we use is a standard one. It is defined in the `Identity-Type` module of the [Type Topology][] library, but apart from syntax it is equivalent to the identity type used in most other Agda libraries.

We make `refl` available by importing it from the `Identity-Type` module.  However, we first repeat the definition here (inside a hidden submodule) for clarity. (See [the remark about hidden modules](Prelude.Equality.html#fn3) in the [third footnote](Prelude.Preliminaries.html#fn3).html#fn1) of the [Prelude.Preliminaries][] module.)

<pre class="Agda">

<a id="1239" class="Keyword">module</a> <a id="hide-refl"></a><a id="1246" href="Prelude.Equality.html#1246" class="Module">hide-refl</a> <a id="1256" class="Symbol">{</a><a id="1257" href="Prelude.Equality.html#1257" class="Bound">𝓤</a> <a id="1259" class="Symbol">:</a> <a id="1261" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1269" class="Symbol">}</a> <a id="1271" class="Keyword">where</a>

 <a id="1279" class="Keyword">data</a> <a id="hide-refl._≡_"></a><a id="1284" href="Prelude.Equality.html#1284" class="Datatype Operator">_≡_</a> <a id="1288" class="Symbol">{</a><a id="1289" href="Prelude.Equality.html#1289" class="Bound">𝓤</a><a id="1290" class="Symbol">}</a> <a id="1292" class="Symbol">{</a><a id="1293" href="Prelude.Equality.html#1293" class="Bound">X</a> <a id="1295" class="Symbol">:</a> <a id="1297" href="Prelude.Equality.html#1289" class="Bound">𝓤</a> <a id="1299" href="Universes.html#403" class="Function Operator">̇</a> <a id="1301" class="Symbol">}</a> <a id="1303" class="Symbol">:</a> <a id="1305" href="Prelude.Equality.html#1293" class="Bound">X</a> <a id="1307" class="Symbol">→</a> <a id="1309" href="Prelude.Equality.html#1293" class="Bound">X</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="Prelude.Equality.html#1289" class="Bound">𝓤</a> <a id="1315" href="Universes.html#403" class="Function Operator">̇</a> <a id="1317" class="Keyword">where</a> <a id="hide-refl._≡_.refl"></a><a id="1323" href="Prelude.Equality.html#1323" class="InductiveConstructor">refl</a> <a id="1328" class="Symbol">:</a> <a id="1330" class="Symbol">{</a><a id="1331" href="Prelude.Equality.html#1331" class="Bound">x</a> <a id="1333" class="Symbol">:</a> <a id="1335" href="Prelude.Equality.html#1293" class="Bound">X</a><a id="1336" class="Symbol">}</a> <a id="1338" class="Symbol">→</a> <a id="1340" href="Prelude.Equality.html#1331" class="Bound">x</a> <a id="1342" href="Prelude.Equality.html#1284" class="Datatype Operator">≡</a> <a id="1344" href="Prelude.Equality.html#1331" class="Bound">x</a>

<a id="1347" class="Keyword">open</a> <a id="1352" class="Keyword">import</a> <a id="1359" href="Identity-Type.html" class="Module">Identity-Type</a> <a id="1373" class="Keyword">renaming</a> <a id="1382" class="Symbol">(</a><a id="1383" href="Identity-Type.html#121" class="Datatype Operator">_≡_</a> <a id="1387" class="Symbol">to</a> <a id="1390" class="Keyword">infix</a> <a id="1396" class="Number">0</a> <a id="_≡_"></a><a id="1398" href="Prelude.Equality.html#1398" class="Datatype Operator">_≡_</a><a id="1401" class="Symbol">)</a> <a id="1403" class="Keyword">public</a>

</pre>

Thus, whenever we need to complete a proof by simply asserting that `x` is definitionally equal to itself, we can invoke `refl`.  If we need to make `x` explicit, we use `refl {x = x}`.

Of course `≡` is an equivalence relation and the formal proof of this fact is trivial. We don't even need to prove reflexivity since it is the defining property of `≡`.  Here are the (trivial) proofs of symmetry and transitivity of `≡`.

<pre class="Agda">

<a id="1862" class="Keyword">module</a> <a id="1869" href="Prelude.Equality.html#1869" class="Module">_</a>  <a id="1872" class="Symbol">{</a><a id="1873" href="Prelude.Equality.html#1873" class="Bound">𝓤</a> <a id="1875" class="Symbol">:</a> <a id="1877" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1885" class="Symbol">}{</a><a id="1887" href="Prelude.Equality.html#1887" class="Bound">X</a> <a id="1889" class="Symbol">:</a> <a id="1891" href="Prelude.Equality.html#1873" class="Bound">𝓤</a> <a id="1893" href="Universes.html#403" class="Function Operator">̇</a> <a id="1895" class="Symbol">}</a>  <a id="1898" class="Keyword">where</a>

 <a id="1906" href="Prelude.Equality.html#1906" class="Function">≡-symmetric</a> <a id="1918" class="Symbol">:</a> <a id="1920" class="Symbol">(</a><a id="1921" href="Prelude.Equality.html#1921" class="Bound">x</a> <a id="1923" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Prelude.Equality.html#1887" class="Bound">X</a><a id="1928" class="Symbol">)</a> <a id="1930" class="Symbol">→</a> <a id="1932" href="Prelude.Equality.html#1921" class="Bound">x</a> <a id="1934" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="1936" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1938" class="Symbol">→</a> <a id="1940" href="Prelude.Equality.html#1923" class="Bound">y</a> <a id="1942" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="1944" href="Prelude.Equality.html#1921" class="Bound">x</a>
 <a id="1947" href="Prelude.Equality.html#1906" class="Function">≡-symmetric</a> <a id="1959" class="Symbol">_</a> <a id="1961" class="Symbol">_</a> <a id="1963" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="1968" class="Symbol">=</a> <a id="1970" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="1977" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="1983" class="Symbol">:</a> <a id="1985" class="Symbol">{</a><a id="1986" href="Prelude.Equality.html#1986" class="Bound">x</a> <a id="1988" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="1990" class="Symbol">:</a> <a id="1992" href="Prelude.Equality.html#1887" class="Bound">X</a><a id="1993" class="Symbol">}</a> <a id="1995" class="Symbol">→</a> <a id="1997" href="Prelude.Equality.html#1986" class="Bound">x</a> <a id="1999" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2001" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="2003" class="Symbol">→</a> <a id="2005" href="Prelude.Equality.html#1988" class="Bound">y</a> <a id="2007" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2009" href="Prelude.Equality.html#1986" class="Bound">x</a>
 <a id="2012" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="2018" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2023" class="Symbol">=</a> <a id="2025" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="2032" href="Prelude.Equality.html#2032" class="Function">≡-transitive</a> <a id="2045" class="Symbol">:</a> <a id="2047" class="Symbol">(</a><a id="2048" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2050" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2052" href="Prelude.Equality.html#2052" class="Bound">z</a> <a id="2054" class="Symbol">:</a> <a id="2056" href="Prelude.Equality.html#1887" class="Bound">X</a><a id="2057" class="Symbol">)</a> <a id="2059" class="Symbol">→</a> <a id="2061" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2063" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2065" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2067" class="Symbol">→</a> <a id="2069" href="Prelude.Equality.html#2050" class="Bound">y</a> <a id="2071" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2073" href="Prelude.Equality.html#2052" class="Bound">z</a> <a id="2075" class="Symbol">→</a> <a id="2077" href="Prelude.Equality.html#2048" class="Bound">x</a> <a id="2079" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2081" href="Prelude.Equality.html#2052" class="Bound">z</a>
 <a id="2084" href="Prelude.Equality.html#2032" class="Function">≡-transitive</a> <a id="2097" class="Symbol">_</a> <a id="2099" class="Symbol">_</a> <a id="2101" class="Symbol">_</a> <a id="2103" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2108" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2113" class="Symbol">=</a> <a id="2115" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

 <a id="2122" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="2130" class="Symbol">:</a> <a id="2132" class="Symbol">{</a><a id="2133" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2135" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2137" href="Prelude.Equality.html#2137" class="Bound">z</a> <a id="2139" class="Symbol">:</a> <a id="2141" href="Prelude.Equality.html#1887" class="Bound">X</a><a id="2142" class="Symbol">}</a> <a id="2144" class="Symbol">→</a> <a id="2146" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2148" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2150" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2152" class="Symbol">→</a> <a id="2154" href="Prelude.Equality.html#2135" class="Bound">y</a> <a id="2156" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2158" href="Prelude.Equality.html#2137" class="Bound">z</a> <a id="2160" class="Symbol">→</a> <a id="2162" href="Prelude.Equality.html#2133" class="Bound">x</a> <a id="2164" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2166" href="Prelude.Equality.html#2137" class="Bound">z</a>
 <a id="2169" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="2177" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2182" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="2187" class="Symbol">=</a> <a id="2189" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

The only difference between `≡-symmetric` and `≡-sym` (respectively, `≡-transitive` and `≡-trans`) is that the latter has fewer explicit arguments, which is sometimes convenient.

Many proofs make abundant use of the symmetry of `_≡_`, and the following syntactic sugar can often improve the readability of such proofs.<sup>[1](Prelude.Equality.html#fn1)</sup>

<pre class="Agda">

<a id="2583" class="Keyword">module</a> <a id="hide-sym-trans"></a><a id="2590" href="Prelude.Equality.html#2590" class="Module">hide-sym-trans</a> <a id="2605" class="Symbol">{</a><a id="2606" href="Prelude.Equality.html#2606" class="Bound">𝓤</a> <a id="2608" class="Symbol">:</a> <a id="2610" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2618" class="Symbol">}</a> <a id="2620" class="Keyword">where</a>

 <a id="hide-sym-trans._⁻¹"></a><a id="2628" href="Prelude.Equality.html#2628" class="Function Operator">_⁻¹</a> <a id="2632" class="Symbol">:</a> <a id="2634" class="Symbol">{</a><a id="2635" href="Prelude.Equality.html#2635" class="Bound">X</a> <a id="2637" class="Symbol">:</a> <a id="2639" href="Prelude.Equality.html#2606" class="Bound">𝓤</a> <a id="2641" href="Universes.html#403" class="Function Operator">̇</a> <a id="2643" class="Symbol">}</a> <a id="2645" class="Symbol">→</a> <a id="2647" class="Symbol">{</a><a id="2648" href="Prelude.Equality.html#2648" class="Bound">x</a> <a id="2650" href="Prelude.Equality.html#2650" class="Bound">y</a> <a id="2652" class="Symbol">:</a> <a id="2654" href="Prelude.Equality.html#2635" class="Bound">X</a><a id="2655" class="Symbol">}</a> <a id="2657" class="Symbol">→</a> <a id="2659" href="Prelude.Equality.html#2648" class="Bound">x</a> <a id="2661" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2663" href="Prelude.Equality.html#2650" class="Bound">y</a> <a id="2665" class="Symbol">→</a> <a id="2667" href="Prelude.Equality.html#2650" class="Bound">y</a> <a id="2669" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2671" href="Prelude.Equality.html#2648" class="Bound">x</a>
 <a id="2674" href="Prelude.Equality.html#2674" class="Bound">p</a> <a id="2676" href="Prelude.Equality.html#2628" class="Function Operator">⁻¹</a> <a id="2679" class="Symbol">=</a> <a id="2681" href="Prelude.Equality.html#1977" class="Function">≡-sym</a> <a id="2687" href="Prelude.Equality.html#2674" class="Bound">p</a>

</pre>

If we have a proof `p : x ≡ y`, and we need a proof of `y ≡ x`, then instead of `≡-sym p` we can use the more intuitive `p ⁻¹` .

Similarly, the following syntactic sugar makes abundant appeals to transitivity easier to stomach.

<pre class="Agda">

 <a id="hide-sym-trans._∙_"></a><a id="2947" href="Prelude.Equality.html#2947" class="Function Operator">_∙_</a> <a id="2951" class="Symbol">:</a> <a id="2953" class="Symbol">{</a><a id="2954" href="Prelude.Equality.html#2954" class="Bound">X</a> <a id="2956" class="Symbol">:</a> <a id="2958" href="Prelude.Equality.html#2606" class="Bound">𝓤</a> <a id="2960" href="Universes.html#403" class="Function Operator">̇</a> <a id="2962" class="Symbol">}</a> <a id="2964" class="Symbol">{</a><a id="2965" href="Prelude.Equality.html#2965" class="Bound">x</a> <a id="2967" href="Prelude.Equality.html#2967" class="Bound">y</a> <a id="2969" href="Prelude.Equality.html#2969" class="Bound">z</a> <a id="2971" class="Symbol">:</a> <a id="2973" href="Prelude.Equality.html#2954" class="Bound">X</a><a id="2974" class="Symbol">}</a> <a id="2976" class="Symbol">→</a> <a id="2978" href="Prelude.Equality.html#2965" class="Bound">x</a> <a id="2980" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2982" href="Prelude.Equality.html#2967" class="Bound">y</a> <a id="2984" class="Symbol">→</a> <a id="2986" href="Prelude.Equality.html#2967" class="Bound">y</a> <a id="2988" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2990" href="Prelude.Equality.html#2969" class="Bound">z</a> <a id="2992" class="Symbol">→</a> <a id="2994" href="Prelude.Equality.html#2965" class="Bound">x</a> <a id="2996" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="2998" href="Prelude.Equality.html#2969" class="Bound">z</a>
 <a id="3001" href="Prelude.Equality.html#3001" class="Bound">p</a> <a id="3003" href="Prelude.Equality.html#2947" class="Function Operator">∙</a> <a id="3005" href="Prelude.Equality.html#3005" class="Bound">q</a> <a id="3007" class="Symbol">=</a> <a id="3009" href="Prelude.Equality.html#2122" class="Function">≡-trans</a> <a id="3017" href="Prelude.Equality.html#3001" class="Bound">p</a> <a id="3019" href="Prelude.Equality.html#3005" class="Bound">q</a>

</pre>

As usual, we import the original definitions from the [Type Topology][] library.

<pre class="Agda">

<a id="3130" class="Keyword">open</a> <a id="3135" class="Keyword">import</a> <a id="3142" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="3151" class="Keyword">using</a> <a id="3157" class="Symbol">(</a><a id="3158" href="MGS-MLTT.html#6125" class="Function Operator">_⁻¹</a><a id="3161" class="Symbol">;</a> <a id="3163" href="MGS-MLTT.html#5910" class="Function Operator">_∙_</a><a id="3166" class="Symbol">)</a> <a id="3168" class="Keyword">public</a>

</pre>

#### <a id="transport">Transport</a>

Alonzo Church characterized equality by declaring two things equal iff no property (predicate) can distinguish them.<sup>[3](Prelude.Equality.html#fn3)</sup>  In other terms, `x` and `y` are equal iff for all `P` we have `P x → P y`.  One direction of this implication is sometimes called *substitution* or *transport* or *transport along an identity*.  It asserts that *if* two objects are equal and one of them satisfies a predicate, then so does the other. A type representing this notion is defined in the `MGS-MLTT` module of the [Type Topology][] library as follows.<sup>[2](Preliminaries.Equality.html#fn2)</sup>

<pre class="Agda">

<a id="3861" class="Keyword">module</a> <a id="hide-transport"></a><a id="3868" href="Prelude.Equality.html#3868" class="Module">hide-transport</a> <a id="3883" class="Symbol">{</a><a id="3884" href="Prelude.Equality.html#3884" class="Bound">𝓤</a> <a id="3886" href="Prelude.Equality.html#3886" class="Bound">𝓦</a> <a id="3888" class="Symbol">:</a> <a id="3890" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3898" class="Symbol">}</a> <a id="3900" class="Keyword">where</a>

 <a id="hide-transport.𝑖𝑑"></a><a id="3908" href="Prelude.Equality.html#3908" class="Function">𝑖𝑑</a> <a id="3911" class="Symbol">:</a> <a id="3913" class="Symbol">{</a><a id="3914" href="Prelude.Equality.html#3914" class="Bound">𝓧</a> <a id="3916" class="Symbol">:</a> <a id="3918" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3926" class="Symbol">}</a> <a id="3928" class="Symbol">(</a><a id="3929" href="Prelude.Equality.html#3929" class="Bound">X</a> <a id="3931" class="Symbol">:</a> <a id="3933" href="Prelude.Equality.html#3914" class="Bound">𝓧</a> <a id="3935" href="Universes.html#403" class="Function Operator">̇</a> <a id="3937" class="Symbol">)</a> <a id="3939" class="Symbol">→</a> <a id="3941" href="Prelude.Equality.html#3929" class="Bound">X</a> <a id="3943" class="Symbol">→</a> <a id="3945" href="Prelude.Equality.html#3929" class="Bound">X</a>
 <a id="3948" href="Prelude.Equality.html#3908" class="Function">𝑖𝑑</a> <a id="3951" href="Prelude.Equality.html#3951" class="Bound">X</a> <a id="3953" class="Symbol">=</a> <a id="3955" class="Symbol">λ</a> <a id="3957" href="Prelude.Equality.html#3957" class="Bound">x</a> <a id="3959" class="Symbol">→</a> <a id="3961" href="Prelude.Equality.html#3957" class="Bound">x</a>

 <a id="hide-transport.transport"></a><a id="3965" href="Prelude.Equality.html#3965" class="Function">transport</a> <a id="3975" class="Symbol">:</a> <a id="3977" class="Symbol">{</a><a id="3978" href="Prelude.Equality.html#3978" class="Bound">X</a> <a id="3980" class="Symbol">:</a> <a id="3982" href="Prelude.Equality.html#3884" class="Bound">𝓤</a> <a id="3984" href="Universes.html#403" class="Function Operator">̇</a> <a id="3986" class="Symbol">}</a> <a id="3988" class="Symbol">(</a><a id="3989" href="Prelude.Equality.html#3989" class="Bound">A</a> <a id="3991" class="Symbol">:</a> <a id="3993" href="Prelude.Equality.html#3978" class="Bound">X</a> <a id="3995" class="Symbol">→</a> <a id="3997" href="Prelude.Equality.html#3886" class="Bound">𝓦</a> <a id="3999" href="Universes.html#403" class="Function Operator">̇</a> <a id="4001" class="Symbol">)</a> <a id="4003" class="Symbol">{</a><a id="4004" href="Prelude.Equality.html#4004" class="Bound">x</a> <a id="4006" href="Prelude.Equality.html#4006" class="Bound">y</a> <a id="4008" class="Symbol">:</a> <a id="4010" href="Prelude.Equality.html#3978" class="Bound">X</a><a id="4011" class="Symbol">}</a> <a id="4013" class="Symbol">→</a> <a id="4015" href="Prelude.Equality.html#4004" class="Bound">x</a> <a id="4017" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4019" href="Prelude.Equality.html#4006" class="Bound">y</a> <a id="4021" class="Symbol">→</a> <a id="4023" href="Prelude.Equality.html#3989" class="Bound">A</a> <a id="4025" href="Prelude.Equality.html#4004" class="Bound">x</a> <a id="4027" class="Symbol">→</a> <a id="4029" href="Prelude.Equality.html#3989" class="Bound">A</a> <a id="4031" href="Prelude.Equality.html#4006" class="Bound">y</a>
 <a id="4034" href="Prelude.Equality.html#3965" class="Function">transport</a> <a id="4044" href="Prelude.Equality.html#4044" class="Bound">A</a> <a id="4046" class="Symbol">(</a><a id="4047" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4052" class="Symbol">{</a><a id="4053" class="Argument">x</a> <a id="4055" class="Symbol">=</a> <a id="4057" href="Prelude.Equality.html#4057" class="Bound">x</a><a id="4058" class="Symbol">})</a> <a id="4061" class="Symbol">=</a> <a id="4063" href="Prelude.Equality.html#3908" class="Function">𝑖𝑑</a> <a id="4066" class="Symbol">(</a><a id="4067" href="Prelude.Equality.html#4044" class="Bound">A</a> <a id="4069" href="Prelude.Equality.html#4057" class="Bound">x</a><a id="4070" class="Symbol">)</a>

<a id="4073" class="Keyword">open</a> <a id="4078" class="Keyword">import</a> <a id="4085" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="4094" class="Keyword">using</a> <a id="4100" class="Symbol">(</a><a id="4101" href="MGS-MLTT.html#3778" class="Function">𝑖𝑑</a><a id="4103" class="Symbol">;</a> <a id="4105" href="MGS-MLTT.html#4946" class="Function">transport</a><a id="4114" class="Symbol">)</a> <a id="4116" class="Keyword">public</a>

</pre>

As usual, we display `transport` in a hidden module and then imported the existing definition from [Type Topology][]. 

A function is well defined if and only if it maps equivalent elements to a single element and we often use this nature of functions in Agda proofs.  If we have a function `f : X → Y`, two elements `a b : X` of the domain, and an identity proof `p : a ≡ b`, then we obtain a proof of `f a ≡ f b` by simply applying the `ap` function like so, `ap f p : f a ≡ f b`. Escardó defines `ap` in the [Type Topology][] library as follows.

<pre class="Agda">

<a id="4700" class="Keyword">module</a> <a id="hide-ap"></a><a id="4707" href="Prelude.Equality.html#4707" class="Module">hide-ap</a>  <a id="4716" class="Symbol">{</a><a id="4717" href="Prelude.Equality.html#4717" class="Bound">𝓤</a> <a id="4719" class="Symbol">:</a> <a id="4721" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4729" class="Symbol">}</a> <a id="4731" class="Keyword">where</a>

 <a id="hide-ap.ap"></a><a id="4739" href="Prelude.Equality.html#4739" class="Function">ap</a> <a id="4742" class="Symbol">:</a> <a id="4744" class="Symbol">{</a><a id="4745" href="Prelude.Equality.html#4745" class="Bound">X</a> <a id="4747" class="Symbol">:</a> <a id="4749" href="Prelude.Equality.html#4717" class="Bound">𝓤</a> <a id="4751" href="Universes.html#403" class="Function Operator">̇</a><a id="4752" class="Symbol">}{</a><a id="4754" href="Prelude.Equality.html#4754" class="Bound">Y</a> <a id="4756" class="Symbol">:</a> <a id="4758" href="Universes.html#262" class="Generalizable">𝓥</a> <a id="4760" href="Universes.html#403" class="Function Operator">̇</a><a id="4761" class="Symbol">}(</a><a id="4763" href="Prelude.Equality.html#4763" class="Bound">f</a> <a id="4765" class="Symbol">:</a> <a id="4767" href="Prelude.Equality.html#4745" class="Bound">X</a> <a id="4769" class="Symbol">→</a> <a id="4771" href="Prelude.Equality.html#4754" class="Bound">Y</a><a id="4772" class="Symbol">){</a><a id="4774" href="Prelude.Equality.html#4774" class="Bound">a</a> <a id="4776" href="Prelude.Equality.html#4776" class="Bound">b</a> <a id="4778" class="Symbol">:</a> <a id="4780" href="Prelude.Equality.html#4745" class="Bound">X</a><a id="4781" class="Symbol">}</a> <a id="4783" class="Symbol">→</a> <a id="4785" href="Prelude.Equality.html#4774" class="Bound">a</a> <a id="4787" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4789" href="Prelude.Equality.html#4776" class="Bound">b</a> <a id="4791" class="Symbol">→</a> <a id="4793" href="Prelude.Equality.html#4763" class="Bound">f</a> <a id="4795" href="Prelude.Equality.html#4774" class="Bound">a</a> <a id="4797" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4799" href="Prelude.Equality.html#4763" class="Bound">f</a> <a id="4801" href="Prelude.Equality.html#4776" class="Bound">b</a>
 <a id="4804" href="Prelude.Equality.html#4739" class="Function">ap</a> <a id="4807" href="Prelude.Equality.html#4807" class="Bound">f</a> <a id="4809" class="Symbol">{</a><a id="4810" href="Prelude.Equality.html#4810" class="Bound">a</a><a id="4811" class="Symbol">}</a> <a id="4813" href="Prelude.Equality.html#4813" class="Bound">p</a> <a id="4815" class="Symbol">=</a> <a id="4817" href="MGS-MLTT.html#4946" class="Function">transport</a> <a id="4827" class="Symbol">(λ</a> <a id="4830" href="Prelude.Equality.html#4830" class="Bound">-</a> <a id="4832" class="Symbol">→</a> <a id="4834" href="Prelude.Equality.html#4807" class="Bound">f</a> <a id="4836" href="Prelude.Equality.html#4810" class="Bound">a</a> <a id="4838" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="4840" href="Prelude.Equality.html#4807" class="Bound">f</a> <a id="4842" href="Prelude.Equality.html#4830" class="Bound">-</a><a id="4843" class="Symbol">)</a> <a id="4845" href="Prelude.Equality.html#4813" class="Bound">p</a> <a id="4847" class="Symbol">(</a><a id="4848" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="4853" class="Symbol">{</a><a id="4854" class="Argument">x</a> <a id="4856" class="Symbol">=</a> <a id="4858" href="Prelude.Equality.html#4807" class="Bound">f</a> <a id="4860" href="Prelude.Equality.html#4810" class="Bound">a</a><a id="4861" class="Symbol">})</a>

<a id="4865" class="Keyword">open</a> <a id="4870" class="Keyword">import</a> <a id="4877" href="MGS-MLTT.html" class="Module">MGS-MLTT</a> <a id="4886" class="Keyword">using</a> <a id="4892" class="Symbol">(</a><a id="4893" href="MGS-MLTT.html#6613" class="Function">ap</a><a id="4895" class="Symbol">)</a> <a id="4897" class="Keyword">public</a>

</pre>

We now define some variations of `ap` that are sometimes useful.

<pre class="Agda">

<a id="4997" class="Keyword">module</a> <a id="5004" href="Prelude.Equality.html#5004" class="Module">_</a> <a id="5006" class="Symbol">{</a><a id="5007" href="Prelude.Equality.html#5007" class="Bound">𝓤</a> <a id="5009" href="Prelude.Equality.html#5009" class="Bound">𝓦</a> <a id="5011" class="Symbol">:</a> <a id="5013" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="5021" class="Symbol">}</a> <a id="5023" class="Keyword">where</a>

 <a id="5031" href="Prelude.Equality.html#5031" class="Function">ap-cong</a> <a id="5039" class="Symbol">:</a> <a id="5041" class="Symbol">{</a><a id="5042" href="Prelude.Equality.html#5042" class="Bound">A</a> <a id="5044" class="Symbol">:</a> <a id="5046" href="Prelude.Equality.html#5007" class="Bound">𝓤</a> <a id="5048" href="Universes.html#403" class="Function Operator">̇</a><a id="5049" class="Symbol">}{</a><a id="5051" href="Prelude.Equality.html#5051" class="Bound">B</a> <a id="5053" class="Symbol">:</a> <a id="5055" href="Prelude.Equality.html#5009" class="Bound">𝓦</a> <a id="5057" href="Universes.html#403" class="Function Operator">̇</a><a id="5058" class="Symbol">}{</a><a id="5060" href="Prelude.Equality.html#5060" class="Bound">f</a> <a id="5062" href="Prelude.Equality.html#5062" class="Bound">g</a> <a id="5064" class="Symbol">:</a> <a id="5066" href="Prelude.Equality.html#5042" class="Bound">A</a> <a id="5068" class="Symbol">→</a> <a id="5070" href="Prelude.Equality.html#5051" class="Bound">B</a><a id="5071" class="Symbol">}{</a><a id="5073" href="Prelude.Equality.html#5073" class="Bound">a</a> <a id="5075" href="Prelude.Equality.html#5075" class="Bound">b</a> <a id="5077" class="Symbol">:</a> <a id="5079" href="Prelude.Equality.html#5042" class="Bound">A</a><a id="5080" class="Symbol">}</a> <a id="5082" class="Symbol">→</a> <a id="5084" href="Prelude.Equality.html#5060" class="Bound">f</a> <a id="5086" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5088" href="Prelude.Equality.html#5062" class="Bound">g</a> <a id="5090" class="Symbol">→</a> <a id="5092" href="Prelude.Equality.html#5073" class="Bound">a</a> <a id="5094" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5096" href="Prelude.Equality.html#5075" class="Bound">b</a> <a id="5098" class="Symbol">→</a> <a id="5100" href="Prelude.Equality.html#5060" class="Bound">f</a> <a id="5102" href="Prelude.Equality.html#5073" class="Bound">a</a> <a id="5104" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5106" href="Prelude.Equality.html#5062" class="Bound">g</a> <a id="5108" href="Prelude.Equality.html#5075" class="Bound">b</a>
 <a id="5111" href="Prelude.Equality.html#5031" class="Function">ap-cong</a> <a id="5119" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5124" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5129" class="Symbol">=</a> <a id="5131" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>

We sometimes need a version of this that works for [dependent types][], such as the following (which we borrow from the `Relation/Binary/Core.agda` module of the [Agda Standard Library][], transcribed into MHE/UALib notation of course):

<pre class="Agda">

 <a id="5402" href="Prelude.Equality.html#5402" class="Function">cong-app</a> <a id="5411" class="Symbol">:</a> <a id="5413" class="Symbol">{</a><a id="5414" href="Prelude.Equality.html#5414" class="Bound">A</a> <a id="5416" class="Symbol">:</a> <a id="5418" href="Prelude.Equality.html#5007" class="Bound">𝓤</a> <a id="5420" href="Universes.html#403" class="Function Operator">̇</a><a id="5421" class="Symbol">}{</a><a id="5423" href="Prelude.Equality.html#5423" class="Bound">B</a> <a id="5425" class="Symbol">:</a> <a id="5427" href="Prelude.Equality.html#5414" class="Bound">A</a> <a id="5429" class="Symbol">→</a> <a id="5431" href="Prelude.Equality.html#5009" class="Bound">𝓦</a> <a id="5433" href="Universes.html#403" class="Function Operator">̇</a><a id="5434" class="Symbol">}{</a><a id="5436" href="Prelude.Equality.html#5436" class="Bound">f</a> <a id="5438" href="Prelude.Equality.html#5438" class="Bound">g</a> <a id="5440" class="Symbol">:</a> <a id="5442" href="MGS-MLTT.html#3562" class="Function">Π</a> <a id="5444" href="Prelude.Equality.html#5423" class="Bound">B</a><a id="5445" class="Symbol">}</a> <a id="5447" class="Symbol">→</a> <a id="5449" href="Prelude.Equality.html#5436" class="Bound">f</a> <a id="5451" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5453" href="Prelude.Equality.html#5438" class="Bound">g</a> <a id="5455" class="Symbol">→</a> <a id="5457" class="Symbol">∀</a> <a id="5459" href="Prelude.Equality.html#5459" class="Bound">a</a> <a id="5461" class="Symbol">→</a> <a id="5463" href="Prelude.Equality.html#5436" class="Bound">f</a> <a id="5465" href="Prelude.Equality.html#5459" class="Bound">a</a> <a id="5467" href="Prelude.Equality.html#1398" class="Datatype Operator">≡</a> <a id="5469" href="Prelude.Equality.html#5438" class="Bound">g</a> <a id="5471" href="Prelude.Equality.html#5459" class="Bound">a</a>
 <a id="5474" href="Prelude.Equality.html#5402" class="Function">cong-app</a> <a id="5483" href="Identity-Type.html#162" class="InductiveConstructor">refl</a> <a id="5488" class="Symbol">_</a> <a id="5490" class="Symbol">=</a> <a id="5492" href="Identity-Type.html#162" class="InductiveConstructor">refl</a>

</pre>




-------------------------------------


<sup>1</sup><span class="footnote" id="fn1"> **Unicode Hints**. In [agda2-mode][] type `⁻¹` as `\^-\^1`, type `𝑖𝑑` as `\Mii\Mid`, and type `∙` as `\.`. In general, to get information about a given unicode character (e.g., how to type it) place the cursor over that character and type `M-x describe-char` (or `M-x h d c`).</span>

<sup>2</sup><span class="footnote" id="fn2"> Alonzo Church, "A Formulation of the Simple Theory of Types," *Journal of Symbolic Logic*, (2)5:56--68, 1940 [JSOR link](http://www.jstor.org/stable/2266170). See also [this section](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#70309) of Escardó's [HoTT/UF in Agda notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html) for a discussion of transport; cf. [HoTT-Agda's definition](https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/Base.agda).<span>

<p></p>
<p></p>


[← Prelude.Preliminaries ](Prelude.Preliminaries.html)
<span style="float:right;">[Prelude.Extensionality →](Prelude.Extensionality.html)</span>

{% include UALib.Links.md %}


<!-- NO LONGER USED

#### <a id="≡-intro-and-≡-elim-for-nondependent-pairs">≡-intro and ≡-elim for nondependent pairs</a>

We conclude the Equality module with some occasionally useful introduction and elimination rules for the equality relation on (nondependent) pair types.

 ≡-elim-left : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → A₁ ≡ A₂
 ≡-elim-left e = ap fst e


 ≡-elim-right : {A₁ A₂ : 𝓤 ̇}{B₁ B₂ : 𝓦 ̇} → (A₁ , B₁) ≡ (A₂ , B₂) → B₁ ≡ B₂
 ≡-elim-right e = ap snd e


 ≡-×-intro : {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓦 ̇} → A₁ ≡ A₂ → B₁ ≡ B₂ → (A₁ , B₁) ≡ (A₂ , B₂)
 ≡-×-intro refl refl = refl


 ≡-×-int : {A : 𝓤 ̇}{B : 𝓦 ̇}{a x : A}{b y : B} → a ≡ x → b ≡ y → (a , b) ≡ (x , y)
 ≡-×-int refl refl = refl

-->
