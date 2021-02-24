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

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1299" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#5703" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#5703" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#5703" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

The product of 𝑆-algebras for the Sigma type representation is defined as follows.

<pre class="Agda">

<a id="⨅"></a><a id="908" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">{</a><a id="913" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="915" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="917" class="Symbol">:</a> <a id="919" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="927" class="Symbol">}{</a><a id="929" href="Algebras.Products.html#929" class="Bound">I</a> <a id="931" class="Symbol">:</a> <a id="933" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="935" href="Universes.html#403" class="Function Operator">̇</a> <a id="937" class="Symbol">}(</a><a id="939" href="Algebras.Products.html#939" class="Bound">𝒜</a> <a id="941" class="Symbol">:</a> <a id="943" href="Algebras.Products.html#929" class="Bound">I</a> <a id="945" class="Symbol">→</a> <a id="947" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="955" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="957" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="959" class="Symbol">)</a> <a id="961" class="Symbol">→</a> <a id="963" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="971" class="Symbol">(</a><a id="972" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="974" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="976" href="Algebras.Products.html#913" class="Bound">𝓤</a><a id="977" class="Symbol">)</a> <a id="979" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="982" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="984" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="986" class="Symbol">=</a> <a id="988" class="Symbol">(∀</a> <a id="991" href="Algebras.Products.html#991" class="Bound">i</a> <a id="993" class="Symbol">→</a> <a id="995" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="997" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="999" href="Algebras.Products.html#991" class="Bound">i</a> <a id="1001" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a><a id="1002" class="Symbol">)</a> <a id="1004" href="Prelude.Equality.html#463" class="InductiveConstructor Operator">,</a>                <a id="1021" class="Comment">-- domain of the product algebra</a>

       <a id="1062" class="Symbol">λ</a> <a id="1064" href="Algebras.Products.html#1064" class="Bound">𝑓</a> <a id="1066" href="Algebras.Products.html#1066" class="Bound">𝑎</a> <a id="1068" href="Algebras.Products.html#1068" class="Bound">i</a> <a id="1070" class="Symbol">→</a> <a id="1072" class="Symbol">(</a><a id="1073" href="Algebras.Products.html#1064" class="Bound">𝑓</a> <a id="1075" href="Algebras.Algebras.html#2844" class="Function Operator">̂</a> <a id="1077" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="1079" href="Algebras.Products.html#1068" class="Bound">i</a><a id="1080" class="Symbol">)</a> <a id="1082" class="Symbol">λ</a> <a id="1084" href="Algebras.Products.html#1084" class="Bound">x</a> <a id="1086" class="Symbol">→</a> <a id="1088" href="Algebras.Products.html#1066" class="Bound">𝑎</a> <a id="1090" href="Algebras.Products.html#1084" class="Bound">x</a> <a id="1092" href="Algebras.Products.html#1068" class="Bound">i</a>  <a id="1095" class="Comment">-- basic operations of the product algebra</a>

</pre>

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1378" class="Keyword">open</a> <a id="1383" href="Algebras.Algebras.html#1850" class="Module">algebra</a>

<a id="1392" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1431" href="Algebras.Products.html#1431" class="Function">⨅&#39;</a> <a id="1434" class="Symbol">:</a> <a id="1436" class="Symbol">{</a><a id="1437" href="Algebras.Products.html#1437" class="Bound">𝓤</a> <a id="1439" href="Algebras.Products.html#1439" class="Bound">𝓘</a> <a id="1441" class="Symbol">:</a> <a id="1443" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1451" class="Symbol">}{</a><a id="1453" href="Algebras.Products.html#1453" class="Bound">I</a> <a id="1455" class="Symbol">:</a> <a id="1457" href="Algebras.Products.html#1439" class="Bound">𝓘</a> <a id="1459" href="Universes.html#403" class="Function Operator">̇</a> <a id="1461" class="Symbol">}(</a><a id="1463" href="Algebras.Products.html#1463" class="Bound">𝒜</a> <a id="1465" class="Symbol">:</a> <a id="1467" href="Algebras.Products.html#1453" class="Bound">I</a> <a id="1469" class="Symbol">→</a> <a id="1471" href="Algebras.Algebras.html#1850" class="Record">algebra</a> <a id="1479" href="Algebras.Products.html#1437" class="Bound">𝓤</a> <a id="1481" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1482" class="Symbol">)</a> <a id="1484" class="Symbol">→</a> <a id="1486" href="Algebras.Algebras.html#1850" class="Record">algebra</a> <a id="1494" class="Symbol">(</a><a id="1495" href="Algebras.Products.html#1439" class="Bound">𝓘</a> <a id="1497" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1499" href="Algebras.Products.html#1437" class="Bound">𝓤</a><a id="1500" class="Symbol">)</a> <a id="1502" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="1505" href="Algebras.Products.html#1431" class="Function">⨅&#39;</a> <a id="1508" href="Algebras.Products.html#1508" class="Bound">𝒜</a> <a id="1510" class="Symbol">=</a> <a id="1512" class="Keyword">record</a> <a id="1519" class="Symbol">{</a> <a id="1521" href="Algebras.Algebras.html#1948" class="Field">univ</a> <a id="1526" class="Symbol">=</a> <a id="1528" class="Symbol">∀</a> <a id="1530" href="Algebras.Products.html#1530" class="Bound">i</a> <a id="1532" class="Symbol">→</a> <a id="1534" href="Algebras.Algebras.html#1948" class="Field">univ</a> <a id="1539" class="Symbol">(</a><a id="1540" href="Algebras.Products.html#1508" class="Bound">𝒜</a> <a id="1542" href="Algebras.Products.html#1530" class="Bound">i</a><a id="1543" class="Symbol">)</a>               <a id="1559" class="Comment">-- domain</a>
               <a id="1584" class="Symbol">;</a> <a id="1586" href="Algebras.Algebras.html#1962" class="Field">op</a> <a id="1589" class="Symbol">=</a> <a id="1591" class="Symbol">λ</a> <a id="1593" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1595" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1597" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1599" class="Symbol">→</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Algebras.Algebras.html#1962" class="Field">op</a> <a id="1605" class="Symbol">(</a><a id="1606" href="Algebras.Products.html#1508" class="Bound">𝒜</a> <a id="1608" href="Algebras.Products.html#1597" class="Bound">i</a><a id="1609" class="Symbol">))</a> <a id="1612" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1614" class="Symbol">λ</a> <a id="1616" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1618" class="Symbol">→</a> <a id="1620" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1622" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1624" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1626" class="Comment">-- basic operations</a>
               <a id="1661" class="Symbol">}</a>

</pre>



#### <a id="notation">Notation</a>

Before proceeding, we define some convenient syntactic sugar. The type `Algebra 𝓤 𝑆` itself has a type; it is `(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ̇` &nbsp;. This type appears quite often throughout the [UALib][], so it is worthwhile to define the following shorthand for its universe level.

<pre class="Agda">

<a id="ov"></a><a id="1999" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="2002" class="Symbol">:</a> <a id="2004" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2013" class="Symbol">→</a> <a id="2015" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2024" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="2027" href="Algebras.Products.html#2027" class="Bound">𝓤</a> <a id="2029" class="Symbol">=</a> <a id="2031" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="2033" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2035" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="2037" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2039" href="Algebras.Products.html#2027" class="Bound">𝓤</a> <a id="2041" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">
<a id="2830" class="Keyword">module</a> <a id="2837" href="Algebras.Products.html#2837" class="Module">_</a> <a id="2839" class="Symbol">{</a><a id="2840" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="2842" href="Algebras.Products.html#2842" class="Bound">𝓧</a> <a id="2844" class="Symbol">:</a> <a id="2846" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2854" class="Symbol">}{</a><a id="2856" href="Algebras.Products.html#2856" class="Bound">X</a> <a id="2858" class="Symbol">:</a> <a id="2860" href="Algebras.Products.html#2842" class="Bound">𝓧</a> <a id="2862" href="Universes.html#403" class="Function Operator">̇</a><a id="2863" class="Symbol">}</a> <a id="2865" class="Keyword">where</a>

 <a id="2873" href="Algebras.Products.html#2873" class="Function">ℑ</a> <a id="2875" class="Symbol">:</a> <a id="2877" href="Relations.Unary.html#1062" class="Function">Pred</a> <a id="2882" class="Symbol">(</a><a id="2883" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2891" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="2893" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2894" class="Symbol">)(</a><a id="2896" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="2899" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="2900" class="Symbol">)</a> <a id="2902" class="Symbol">→</a> <a id="2904" class="Symbol">(</a><a id="2905" href="Algebras.Products.html#2842" class="Bound">𝓧</a> <a id="2907" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2909" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="2912" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="2913" class="Symbol">)</a> <a id="2915" href="Universes.html#403" class="Function Operator">̇</a>

 <a id="2919" href="Algebras.Products.html#2873" class="Function">ℑ</a> <a id="2921" href="Algebras.Products.html#2921" class="Bound">𝒦</a> <a id="2923" class="Symbol">=</a> <a id="2925" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="2927" href="Algebras.Products.html#2927" class="Bound">𝑨</a> <a id="2929" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="2931" class="Symbol">(</a><a id="2932" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2940" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="2942" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2943" class="Symbol">)</a> <a id="2945" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="2947" class="Symbol">(</a><a id="2948" href="Algebras.Products.html#2927" class="Bound">𝑨</a> <a id="2950" href="Relations.Unary.html#2061" class="Function Operator">∈</a> <a id="2952" href="Algebras.Products.html#2921" class="Bound">𝒦</a><a id="2953" class="Symbol">)</a> <a id="2955" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="2957" class="Symbol">(</a><a id="2958" href="Algebras.Products.html#2856" class="Bound">X</a> <a id="2960" class="Symbol">→</a> <a id="2962" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="2964" href="Algebras.Products.html#2927" class="Bound">𝑨</a> <a id="2966" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a><a id="2967" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context and we want to keep the context completely general.  Including this context map in the index type ℑ accomplishes this.

Taking the product over the index type ℑ requires a function that takes an index `i : ℑ` and returns the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="3818" href="Algebras.Products.html#3818" class="Function">𝔄</a> <a id="3820" class="Symbol">:</a> <a id="3822" class="Symbol">(</a><a id="3823" href="Algebras.Products.html#3823" class="Bound">𝒦</a> <a id="3825" class="Symbol">:</a> <a id="3827" href="Relations.Unary.html#1062" class="Function">Pred</a> <a id="3832" class="Symbol">(</a><a id="3833" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3841" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="3843" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3844" class="Symbol">)(</a><a id="3846" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="3849" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="3850" class="Symbol">))</a> <a id="3853" class="Symbol">→</a> <a id="3855" href="Algebras.Products.html#2873" class="Function">ℑ</a> <a id="3857" href="Algebras.Products.html#3823" class="Bound">𝒦</a> <a id="3859" class="Symbol">→</a> <a id="3861" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3869" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="3871" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="3875" href="Algebras.Products.html#3818" class="Function">𝔄</a> <a id="3877" href="Algebras.Products.html#3877" class="Bound">𝒦</a> <a id="3879" class="Symbol">=</a> <a id="3881" class="Symbol">λ</a> <a id="3883" class="Symbol">(</a><a id="3884" href="Algebras.Products.html#3884" class="Bound">i</a> <a id="3886" class="Symbol">:</a> <a id="3888" class="Symbol">(</a><a id="3889" href="Algebras.Products.html#2873" class="Function">ℑ</a> <a id="3891" href="Algebras.Products.html#3877" class="Bound">𝒦</a><a id="3892" class="Symbol">))</a> <a id="3895" class="Symbol">→</a> <a id="3897" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="3899" href="Algebras.Products.html#3884" class="Bound">i</a> <a id="3901" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="4017" href="Algebras.Products.html#4017" class="Function">class-product</a> <a id="4031" class="Symbol">:</a> <a id="4033" href="Relations.Unary.html#1062" class="Function">Pred</a> <a id="4038" class="Symbol">(</a><a id="4039" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4047" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="4049" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4050" class="Symbol">)(</a><a id="4052" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="4055" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="4056" class="Symbol">)</a> <a id="4058" class="Symbol">→</a> <a id="4060" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4068" class="Symbol">(</a><a id="4069" href="Algebras.Products.html#2842" class="Bound">𝓧</a> <a id="4071" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4073" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="4076" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="4077" class="Symbol">)</a> <a id="4079" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4083" href="Algebras.Products.html#4017" class="Function">class-product</a> <a id="4097" href="Algebras.Products.html#4097" class="Bound">𝒦</a> <a id="4099" class="Symbol">=</a> <a id="4101" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4103" class="Symbol">(</a> <a id="4105" href="Algebras.Products.html#3818" class="Function">𝔄</a> <a id="4107" href="Algebras.Products.html#4097" class="Bound">𝒦</a> <a id="4109" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4249" href="Algebras.Products.html#4249" class="Function">class-product&#39;</a> <a id="4264" class="Symbol">:</a> <a id="4266" href="Relations.Unary.html#1062" class="Function">Pred</a> <a id="4271" class="Symbol">(</a><a id="4272" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4280" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="4282" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4283" class="Symbol">)(</a><a id="4285" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="4288" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="4289" class="Symbol">)</a> <a id="4291" class="Symbol">→</a> <a id="4293" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4301" class="Symbol">(</a><a id="4302" href="Algebras.Products.html#2842" class="Bound">𝓧</a> <a id="4304" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4306" href="Algebras.Products.html#1999" class="Function">ov</a> <a id="4309" href="Algebras.Products.html#2840" class="Bound">𝓤</a><a id="4310" class="Symbol">)</a> <a id="4312" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4316" href="Algebras.Products.html#4249" class="Function">class-product&#39;</a> <a id="4331" href="Algebras.Products.html#4331" class="Bound">𝒦</a> <a id="4333" class="Symbol">=</a> <a id="4335" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4337" class="Symbol">λ</a> <a id="4339" class="Symbol">(</a><a id="4340" href="Algebras.Products.html#4340" class="Bound">i</a> <a id="4342" class="Symbol">:</a> <a id="4344" class="Symbol">(</a><a id="4345" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4347" href="Algebras.Products.html#4347" class="Bound">𝑨</a> <a id="4349" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4351" class="Symbol">(</a><a id="4352" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4360" href="Algebras.Products.html#2840" class="Bound">𝓤</a> <a id="4362" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4363" class="Symbol">)</a> <a id="4365" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4367" class="Symbol">(</a><a id="4368" href="Algebras.Products.html#4347" class="Bound">𝑨</a> <a id="4370" href="Relations.Unary.html#2061" class="Function Operator">∈</a> <a id="4372" href="Algebras.Products.html#4331" class="Bound">𝒦</a><a id="4373" class="Symbol">)</a> <a id="4375" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4377" class="Symbol">(</a><a id="4378" href="Algebras.Products.html#2856" class="Bound">X</a> <a id="4380" class="Symbol">→</a> <a id="4382" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="4384" href="Algebras.Products.html#4347" class="Bound">𝑨</a> <a id="4386" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a><a id="4387" class="Symbol">)))</a> <a id="4391" class="Symbol">→</a> <a id="4393" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a> <a id="4395" href="Algebras.Products.html#4340" class="Bound">i</a> <a id="4397" href="Prelude.Preliminaries.html#13609" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
