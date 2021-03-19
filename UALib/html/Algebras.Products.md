---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This section presents the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="587" class="Symbol">{-#</a> <a id="591" class="Keyword">OPTIONS</a> <a id="599" class="Pragma">--without-K</a> <a id="611" class="Pragma">--exact-split</a> <a id="625" class="Pragma">--safe</a> <a id="632" class="Symbol">#-}</a>

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1299" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

The product of 𝑆-algebras for the Sigma type representation is defined as follows.

<pre class="Agda">

<a id="⨅"></a><a id="908" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">{</a><a id="913" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="915" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="917" class="Symbol">:</a> <a id="919" href="Universes.html#205" class="Postulate">Universe</a><a id="927" class="Symbol">}{</a><a id="929" href="Algebras.Products.html#929" class="Bound">I</a> <a id="931" class="Symbol">:</a> <a id="933" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="935" href="Universes.html#403" class="Function Operator">̇</a> <a id="937" class="Symbol">}(</a><a id="939" href="Algebras.Products.html#939" class="Bound">𝒜</a> <a id="941" class="Symbol">:</a> <a id="943" href="Algebras.Products.html#929" class="Bound">I</a> <a id="945" class="Symbol">→</a> <a id="947" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="955" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="957" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="959" class="Symbol">)</a> <a id="961" class="Symbol">→</a> <a id="963" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="971" class="Symbol">(</a><a id="972" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="974" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="976" href="Algebras.Products.html#913" class="Bound">𝓤</a><a id="977" class="Symbol">)</a> <a id="979" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="982" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="984" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="986" class="Symbol">=</a> <a id="988" class="Symbol">(∀</a> <a id="991" href="Algebras.Products.html#991" class="Bound">i</a> <a id="993" class="Symbol">→</a> <a id="995" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a> <a id="997" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="999" href="Algebras.Products.html#991" class="Bound">i</a> <a id="1001" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a><a id="1002" class="Symbol">)</a> <a id="1004" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a>               <a id="1020" class="Comment">-- domain of the product algebra</a>

       <a id="1061" class="Symbol">λ</a> <a id="1063" href="Algebras.Products.html#1063" class="Bound">𝑓</a> <a id="1065" href="Algebras.Products.html#1065" class="Bound">𝑎</a> <a id="1067" href="Algebras.Products.html#1067" class="Bound">i</a> <a id="1069" class="Symbol">→</a> <a id="1071" class="Symbol">(</a><a id="1072" href="Algebras.Products.html#1063" class="Bound">𝑓</a> <a id="1074" href="Algebras.Algebras.html#2991" class="Function Operator">̂</a> <a id="1076" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="1078" href="Algebras.Products.html#1067" class="Bound">i</a><a id="1079" class="Symbol">)</a> <a id="1081" class="Symbol">λ</a> <a id="1083" href="Algebras.Products.html#1083" class="Bound">x</a> <a id="1085" class="Symbol">→</a> <a id="1087" href="Algebras.Products.html#1065" class="Bound">𝑎</a> <a id="1089" href="Algebras.Products.html#1083" class="Bound">x</a> <a id="1091" href="Algebras.Products.html#1067" class="Bound">i</a>  <a id="1094" class="Comment">-- basic operations of the product algebra</a>

</pre>

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1377" class="Keyword">open</a> <a id="1382" href="Algebras.Algebras.html#1844" class="Module">algebra</a>

<a id="1391" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1430" href="Algebras.Products.html#1430" class="Function">⨅&#39;</a> <a id="1433" class="Symbol">:</a> <a id="1435" class="Symbol">{</a><a id="1436" href="Algebras.Products.html#1436" class="Bound">𝓤</a> <a id="1438" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1440" class="Symbol">:</a> <a id="1442" href="Universes.html#205" class="Postulate">Universe</a><a id="1450" class="Symbol">}{</a><a id="1452" href="Algebras.Products.html#1452" class="Bound">I</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1458" href="Universes.html#403" class="Function Operator">̇</a> <a id="1460" class="Symbol">}(</a><a id="1462" href="Algebras.Products.html#1462" class="Bound">𝒜</a> <a id="1464" class="Symbol">:</a> <a id="1466" href="Algebras.Products.html#1452" class="Bound">I</a> <a id="1468" class="Symbol">→</a> <a id="1470" href="Algebras.Algebras.html#1844" class="Record">algebra</a> <a id="1478" href="Algebras.Products.html#1436" class="Bound">𝓤</a> <a id="1480" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1481" class="Symbol">)</a> <a id="1483" class="Symbol">→</a> <a id="1485" href="Algebras.Algebras.html#1844" class="Record">algebra</a> <a id="1493" class="Symbol">(</a><a id="1494" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1496" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1498" href="Algebras.Products.html#1436" class="Bound">𝓤</a><a id="1499" class="Symbol">)</a> <a id="1501" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="1504" href="Algebras.Products.html#1430" class="Function">⨅&#39;</a> <a id="1507" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1509" class="Symbol">=</a> <a id="1511" class="Keyword">record</a> <a id="1518" class="Symbol">{</a> <a id="1520" href="Algebras.Algebras.html#1942" class="Field">univ</a> <a id="1525" class="Symbol">=</a> <a id="1527" class="Symbol">∀</a> <a id="1529" href="Algebras.Products.html#1529" class="Bound">i</a> <a id="1531" class="Symbol">→</a> <a id="1533" href="Algebras.Algebras.html#1942" class="Field">univ</a> <a id="1538" class="Symbol">(</a><a id="1539" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1541" href="Algebras.Products.html#1529" class="Bound">i</a><a id="1542" class="Symbol">)</a>                <a id="1559" class="Comment">-- domain</a>
               <a id="1584" class="Symbol">;</a> <a id="1586" href="Algebras.Algebras.html#1956" class="Field">op</a> <a id="1589" class="Symbol">=</a> <a id="1591" class="Symbol">λ</a> <a id="1593" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1595" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1597" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1599" class="Symbol">→</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Algebras.Algebras.html#1956" class="Field">op</a> <a id="1605" class="Symbol">(</a><a id="1606" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1608" href="Algebras.Products.html#1597" class="Bound">i</a><a id="1609" class="Symbol">))</a> <a id="1612" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1614" class="Symbol">λ</a> <a id="1616" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1618" class="Symbol">→</a> <a id="1620" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1622" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1624" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1626" class="Comment">-- basic operations</a>
               <a id="1661" class="Symbol">}</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="1918" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="Universes.html#205" class="Postulate">Universe</a> <a id="1932" class="Symbol">→</a> <a id="1934" href="Universes.html#205" class="Postulate">Universe</a>
<a id="1943" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="1946" href="Algebras.Products.html#1946" class="Bound">𝓤</a> <a id="1948" class="Symbol">=</a> <a id="1950" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="1952" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1954" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="1956" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1958" href="Algebras.Products.html#1946" class="Bound">𝓤</a> <a id="1960" href="Universes.html#181" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">

<a id="2750" class="Keyword">module</a> <a id="2757" href="Algebras.Products.html#2757" class="Module">_</a> <a id="2759" class="Symbol">{</a><a id="2760" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="2762" href="Algebras.Products.html#2762" class="Bound">𝓧</a> <a id="2764" class="Symbol">:</a> <a id="2766" href="Universes.html#205" class="Postulate">Universe</a><a id="2774" class="Symbol">}{</a><a id="2776" href="Algebras.Products.html#2776" class="Bound">X</a> <a id="2778" class="Symbol">:</a> <a id="2780" href="Algebras.Products.html#2762" class="Bound">𝓧</a> <a id="2782" href="Universes.html#403" class="Function Operator">̇</a><a id="2783" class="Symbol">}</a> <a id="2785" class="Keyword">where</a>

 <a id="2793" href="Algebras.Products.html#2793" class="Function">ℑ</a> <a id="2795" class="Symbol">:</a> <a id="2797" href="Relations.Discrete.html#1603" class="Function">Pred</a> <a id="2802" class="Symbol">(</a><a id="2803" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2811" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="2813" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2814" class="Symbol">)(</a><a id="2816" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="2819" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="2820" class="Symbol">)</a> <a id="2822" class="Symbol">→</a> <a id="2824" class="Symbol">(</a><a id="2825" href="Algebras.Products.html#2762" class="Bound">𝓧</a> <a id="2827" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2829" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="2832" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="2833" class="Symbol">)</a> <a id="2835" href="Universes.html#403" class="Function Operator">̇</a>

 <a id="2839" href="Algebras.Products.html#2793" class="Function">ℑ</a> <a id="2841" href="Algebras.Products.html#2841" class="Bound">𝒦</a> <a id="2843" class="Symbol">=</a> <a id="2845" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="2847" href="Algebras.Products.html#2847" class="Bound">𝑨</a> <a id="2849" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="2851" class="Symbol">(</a><a id="2852" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2860" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="2862" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2863" class="Symbol">)</a> <a id="2865" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="2867" class="Symbol">(</a><a id="2868" href="Algebras.Products.html#2847" class="Bound">𝑨</a> <a id="2870" href="Relations.Discrete.html#2413" class="Function Operator">∈</a> <a id="2872" href="Algebras.Products.html#2841" class="Bound">𝒦</a><a id="2873" class="Symbol">)</a> <a id="2875" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="2877" class="Symbol">(</a><a id="2878" href="Algebras.Products.html#2776" class="Bound">X</a> <a id="2880" class="Symbol">→</a> <a id="2882" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a> <a id="2884" href="Algebras.Products.html#2847" class="Bound">𝑨</a> <a id="2886" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a><a id="2887" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why, but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in `X`.  When computing with or reasoning about products, while we don't want to rigidly impose a context in advance, want do want to lay our hands on whatever context is ultimately assumed.  Including the "context map" inside the index type `ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="4023" href="Algebras.Products.html#4023" class="Function">𝔄</a> <a id="4025" class="Symbol">:</a> <a id="4027" class="Symbol">(</a><a id="4028" href="Algebras.Products.html#4028" class="Bound">𝒦</a> <a id="4030" class="Symbol">:</a> <a id="4032" href="Relations.Discrete.html#1603" class="Function">Pred</a> <a id="4037" class="Symbol">(</a><a id="4038" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4046" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="4048" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4049" class="Symbol">)(</a><a id="4051" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4054" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="4055" class="Symbol">))</a> <a id="4058" class="Symbol">→</a> <a id="4060" href="Algebras.Products.html#2793" class="Function">ℑ</a> <a id="4062" href="Algebras.Products.html#4028" class="Bound">𝒦</a> <a id="4064" class="Symbol">→</a> <a id="4066" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4074" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="4076" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4080" href="Algebras.Products.html#4023" class="Function">𝔄</a> <a id="4082" href="Algebras.Products.html#4082" class="Bound">𝒦</a> <a id="4084" class="Symbol">=</a> <a id="4086" class="Symbol">λ</a> <a id="4088" class="Symbol">(</a><a id="4089" href="Algebras.Products.html#4089" class="Bound">i</a> <a id="4091" class="Symbol">:</a> <a id="4093" class="Symbol">(</a><a id="4094" href="Algebras.Products.html#2793" class="Function">ℑ</a> <a id="4096" href="Algebras.Products.html#4082" class="Bound">𝒦</a><a id="4097" class="Symbol">))</a> <a id="4100" class="Symbol">→</a> <a id="4102" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a> <a id="4104" href="Algebras.Products.html#4089" class="Bound">i</a> <a id="4106" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="4222" href="Algebras.Products.html#4222" class="Function">class-product</a> <a id="4236" class="Symbol">:</a> <a id="4238" href="Relations.Discrete.html#1603" class="Function">Pred</a> <a id="4243" class="Symbol">(</a><a id="4244" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4252" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="4254" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4255" class="Symbol">)(</a><a id="4257" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4260" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="4261" class="Symbol">)</a> <a id="4263" class="Symbol">→</a> <a id="4265" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4273" class="Symbol">(</a><a id="4274" href="Algebras.Products.html#2762" class="Bound">𝓧</a> <a id="4276" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4278" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4281" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="4282" class="Symbol">)</a> <a id="4284" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4288" href="Algebras.Products.html#4222" class="Function">class-product</a> <a id="4302" href="Algebras.Products.html#4302" class="Bound">𝒦</a> <a id="4304" class="Symbol">=</a> <a id="4306" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4308" class="Symbol">(</a> <a id="4310" href="Algebras.Products.html#4023" class="Function">𝔄</a> <a id="4312" href="Algebras.Products.html#4302" class="Bound">𝒦</a> <a id="4314" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4454" href="Algebras.Products.html#4454" class="Function">class-product&#39;</a> <a id="4469" class="Symbol">:</a> <a id="4471" href="Relations.Discrete.html#1603" class="Function">Pred</a> <a id="4476" class="Symbol">(</a><a id="4477" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4485" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="4487" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4488" class="Symbol">)(</a><a id="4490" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4493" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="4494" class="Symbol">)</a> <a id="4496" class="Symbol">→</a> <a id="4498" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4506" class="Symbol">(</a><a id="4507" href="Algebras.Products.html#2762" class="Bound">𝓧</a> <a id="4509" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4511" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4514" href="Algebras.Products.html#2760" class="Bound">𝓤</a><a id="4515" class="Symbol">)</a> <a id="4517" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4521" href="Algebras.Products.html#4454" class="Function">class-product&#39;</a> <a id="4536" href="Algebras.Products.html#4536" class="Bound">𝒦</a> <a id="4538" class="Symbol">=</a> <a id="4540" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4542" class="Symbol">λ</a> <a id="4544" class="Symbol">(</a><a id="4545" href="Algebras.Products.html#4545" class="Bound">i</a> <a id="4547" class="Symbol">:</a> <a id="4549" class="Symbol">(</a><a id="4550" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4552" href="Algebras.Products.html#4552" class="Bound">𝑨</a> <a id="4554" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4556" class="Symbol">(</a><a id="4557" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4565" href="Algebras.Products.html#2760" class="Bound">𝓤</a> <a id="4567" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4568" class="Symbol">)</a> <a id="4570" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4572" class="Symbol">(</a><a id="4573" href="Algebras.Products.html#4552" class="Bound">𝑨</a> <a id="4575" href="Relations.Discrete.html#2413" class="Function Operator">∈</a> <a id="4577" href="Algebras.Products.html#4536" class="Bound">𝒦</a><a id="4578" class="Symbol">)</a> <a id="4580" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4582" class="Symbol">(</a><a id="4583" href="Algebras.Products.html#2776" class="Bound">X</a> <a id="4585" class="Symbol">→</a> <a id="4587" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a> <a id="4589" href="Algebras.Products.html#4552" class="Bound">𝑨</a> <a id="4591" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a><a id="4592" class="Symbol">)))</a> <a id="4596" class="Symbol">→</a> <a id="4598" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a> <a id="4600" href="Algebras.Products.html#4545" class="Bound">i</a> <a id="4602" href="Prelude.Preliminaries.html#12384" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
