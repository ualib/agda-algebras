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

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1266" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1266" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

The product of 𝑆-algebras for the Sigma type representation is defined as follows.

<pre class="Agda">

<a id="908" class="Keyword">module</a> <a id="915" href="Algebras.Products.html#915" class="Module">_</a> <a id="917" class="Symbol">{</a><a id="918" href="Algebras.Products.html#918" class="Bound">𝓤</a> <a id="920" href="Algebras.Products.html#920" class="Bound">𝓘</a> <a id="922" class="Symbol">:</a> <a id="924" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="932" class="Symbol">}{</a><a id="934" href="Algebras.Products.html#934" class="Bound">I</a> <a id="936" class="Symbol">:</a> <a id="938" href="Algebras.Products.html#920" class="Bound">𝓘</a> <a id="940" href="Universes.html#403" class="Function Operator">̇</a> <a id="942" class="Symbol">}</a> <a id="944" class="Keyword">where</a>

 <a id="952" href="Algebras.Products.html#952" class="Function">⨅</a> <a id="954" class="Symbol">:</a> <a id="956" class="Symbol">(</a><a id="957" href="Algebras.Products.html#957" class="Bound">𝒜</a> <a id="959" class="Symbol">:</a> <a id="961" href="Algebras.Products.html#934" class="Bound">I</a> <a id="963" class="Symbol">→</a> <a id="965" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="973" href="Algebras.Products.html#918" class="Bound">𝓤</a> <a id="975" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="977" class="Symbol">)</a> <a id="979" class="Symbol">→</a> <a id="981" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="989" class="Symbol">(</a><a id="990" href="Algebras.Products.html#920" class="Bound">𝓘</a> <a id="992" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="994" href="Algebras.Products.html#918" class="Bound">𝓤</a><a id="995" class="Symbol">)</a> <a id="997" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="1001" href="Algebras.Products.html#952" class="Function">⨅</a> <a id="1003" href="Algebras.Products.html#1003" class="Bound">𝒜</a> <a id="1005" class="Symbol">=</a> <a id="1007" class="Symbol">(</a><a id="1008" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1010" href="Algebras.Products.html#1010" class="Bound">i</a> <a id="1012" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1014" href="Algebras.Products.html#934" class="Bound">I</a> <a id="1016" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1018" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="1020" href="Algebras.Products.html#1003" class="Bound">𝒜</a> <a id="1022" href="Algebras.Products.html#1010" class="Bound">i</a> <a id="1024" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="1025" class="Symbol">)</a> <a id="1027" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a>               <a id="1043" class="Comment">-- domain of the product algebra</a>
        <a id="1084" class="Symbol">λ</a> <a id="1086" href="Algebras.Products.html#1086" class="Bound">𝑓</a> <a id="1088" href="Algebras.Products.html#1088" class="Bound">𝑎</a> <a id="1090" href="Algebras.Products.html#1090" class="Bound">i</a> <a id="1092" class="Symbol">→</a> <a id="1094" class="Symbol">(</a><a id="1095" href="Algebras.Products.html#1086" class="Bound">𝑓</a> <a id="1097" href="Algebras.Algebras.html#2912" class="Function Operator">̂</a> <a id="1099" href="Algebras.Products.html#1003" class="Bound">𝒜</a> <a id="1101" href="Algebras.Products.html#1090" class="Bound">i</a><a id="1102" class="Symbol">)</a> <a id="1104" class="Symbol">λ</a> <a id="1106" href="Algebras.Products.html#1106" class="Bound">x</a> <a id="1108" class="Symbol">→</a> <a id="1110" href="Algebras.Products.html#1088" class="Bound">𝑎</a> <a id="1112" href="Algebras.Products.html#1106" class="Bound">x</a> <a id="1114" href="Algebras.Products.html#1090" class="Bound">i</a>  <a id="1117" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1485" class="Keyword">open</a> <a id="1490" href="Algebras.Algebras.html#1788" class="Module">algebra</a>

<a id="1499" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1538" href="Algebras.Products.html#1538" class="Function">⨅&#39;</a> <a id="1541" class="Symbol">:</a> <a id="1543" class="Symbol">{</a><a id="1544" href="Algebras.Products.html#1544" class="Bound">𝓤</a> <a id="1546" href="Algebras.Products.html#1546" class="Bound">𝓘</a> <a id="1548" class="Symbol">:</a> <a id="1550" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1558" class="Symbol">}{</a><a id="1560" href="Algebras.Products.html#1560" class="Bound">I</a> <a id="1562" class="Symbol">:</a> <a id="1564" href="Algebras.Products.html#1546" class="Bound">𝓘</a> <a id="1566" href="Universes.html#403" class="Function Operator">̇</a> <a id="1568" class="Symbol">}(</a><a id="1570" href="Algebras.Products.html#1570" class="Bound">𝒜</a> <a id="1572" class="Symbol">:</a> <a id="1574" href="Algebras.Products.html#1560" class="Bound">I</a> <a id="1576" class="Symbol">→</a> <a id="1578" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="1586" href="Algebras.Products.html#1544" class="Bound">𝓤</a> <a id="1588" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1589" class="Symbol">)</a> <a id="1591" class="Symbol">→</a> <a id="1593" href="Algebras.Algebras.html#1788" class="Record">algebra</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Algebras.Products.html#1546" class="Bound">𝓘</a> <a id="1604" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1606" href="Algebras.Products.html#1544" class="Bound">𝓤</a><a id="1607" class="Symbol">)</a> <a id="1609" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="1612" href="Algebras.Products.html#1538" class="Function">⨅&#39;</a> <a id="1615" href="Algebras.Products.html#1615" class="Bound">𝒜</a> <a id="1617" class="Symbol">=</a> <a id="1619" class="Keyword">record</a> <a id="1626" class="Symbol">{</a> <a id="1628" href="Algebras.Algebras.html#1883" class="Field">univ</a> <a id="1633" class="Symbol">=</a> <a id="1635" class="Symbol">∀</a> <a id="1637" href="Algebras.Products.html#1637" class="Bound">i</a> <a id="1639" class="Symbol">→</a> <a id="1641" href="Algebras.Algebras.html#1883" class="Field">univ</a> <a id="1646" class="Symbol">(</a><a id="1647" href="Algebras.Products.html#1615" class="Bound">𝒜</a> <a id="1649" href="Algebras.Products.html#1637" class="Bound">i</a><a id="1650" class="Symbol">)</a>                <a id="1667" class="Comment">-- domain</a>
               <a id="1692" class="Symbol">;</a> <a id="1694" href="Algebras.Algebras.html#1896" class="Field">op</a> <a id="1697" class="Symbol">=</a> <a id="1699" class="Symbol">λ</a> <a id="1701" href="Algebras.Products.html#1701" class="Bound">𝑓</a> <a id="1703" href="Algebras.Products.html#1703" class="Bound">𝑎</a> <a id="1705" href="Algebras.Products.html#1705" class="Bound">i</a> <a id="1707" class="Symbol">→</a> <a id="1709" class="Symbol">(</a><a id="1710" href="Algebras.Algebras.html#1896" class="Field">op</a> <a id="1713" class="Symbol">(</a><a id="1714" href="Algebras.Products.html#1615" class="Bound">𝒜</a> <a id="1716" href="Algebras.Products.html#1705" class="Bound">i</a><a id="1717" class="Symbol">))</a> <a id="1720" href="Algebras.Products.html#1701" class="Bound">𝑓</a> <a id="1722" class="Symbol">λ</a> <a id="1724" href="Algebras.Products.html#1724" class="Bound">x</a> <a id="1726" class="Symbol">→</a> <a id="1728" href="Algebras.Products.html#1703" class="Bound">𝑎</a> <a id="1730" href="Algebras.Products.html#1724" class="Bound">x</a> <a id="1732" href="Algebras.Products.html#1705" class="Bound">i</a> <a id="1734" class="Comment">-- basic operations</a>
               <a id="1769" class="Symbol">}</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2026" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2040" class="Symbol">→</a> <a id="2042" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2051" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="2054" href="Algebras.Products.html#2054" class="Bound">𝓤</a> <a id="2056" class="Symbol">=</a> <a id="2058" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="2060" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2062" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="2064" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2066" href="Algebras.Products.html#2054" class="Bound">𝓤</a> <a id="2068" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">

<a id="2858" class="Keyword">module</a> <a id="2865" href="Algebras.Products.html#2865" class="Module">_</a> <a id="2867" class="Symbol">{</a><a id="2868" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="2870" href="Algebras.Products.html#2870" class="Bound">𝓧</a> <a id="2872" class="Symbol">:</a> <a id="2874" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2882" class="Symbol">}{</a><a id="2884" href="Algebras.Products.html#2884" class="Bound">X</a> <a id="2886" class="Symbol">:</a> <a id="2888" href="Algebras.Products.html#2870" class="Bound">𝓧</a> <a id="2890" href="Universes.html#403" class="Function Operator">̇</a><a id="2891" class="Symbol">}</a> <a id="2893" class="Keyword">where</a>

 <a id="2901" href="Algebras.Products.html#2901" class="Function">ℑ</a> <a id="2903" class="Symbol">:</a> <a id="2905" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="2910" class="Symbol">(</a><a id="2911" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2919" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="2921" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2922" class="Symbol">)(</a><a id="2924" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="2927" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="2928" class="Symbol">)</a> <a id="2930" class="Symbol">→</a> <a id="2932" class="Symbol">(</a><a id="2933" href="Algebras.Products.html#2870" class="Bound">𝓧</a> <a id="2935" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2937" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="2940" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="2941" class="Symbol">)</a> <a id="2943" href="Universes.html#403" class="Function Operator">̇</a>

 <a id="2947" href="Algebras.Products.html#2901" class="Function">ℑ</a> <a id="2949" href="Algebras.Products.html#2949" class="Bound">𝒦</a> <a id="2951" class="Symbol">=</a> <a id="2953" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="2955" href="Algebras.Products.html#2955" class="Bound">𝑨</a> <a id="2957" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="2959" class="Symbol">(</a><a id="2960" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="2968" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="2970" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2971" class="Symbol">)</a> <a id="2973" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="2975" class="Symbol">(</a><a id="2976" href="Algebras.Products.html#2955" class="Bound">𝑨</a> <a id="2978" href="Relations.Discrete.html#2499" class="Function Operator">∈</a> <a id="2980" href="Algebras.Products.html#2949" class="Bound">𝒦</a><a id="2981" class="Symbol">)</a> <a id="2983" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="2985" class="Symbol">(</a><a id="2986" href="Algebras.Products.html#2884" class="Bound">X</a> <a id="2988" class="Symbol">→</a> <a id="2990" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="2992" href="Algebras.Products.html#2955" class="Bound">𝑨</a> <a id="2994" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="2995" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is  `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`. In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`, until we realized that adding the type `X → ∣ 𝑨 ∣` is quite useful. Later we will see exactly why, but for now suffice it to say that a map of type `X → ∣ 𝑨 ∣` may be viewed abstractly as an *ambient context*, or more concretely, as an assignment of *values* in `∣ 𝑨 ∣` to *variable symbols* in `X`.  When computing with or reasoning about products, while we don't want to rigidly impose a context in advance, want do want to lay our hands on whatever context is ultimately assumed.  Including the "context map" inside the index type `ℑ` of the product turns out to be a convenient way to achieve this flexibility.


Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="4131" href="Algebras.Products.html#4131" class="Function">𝔄</a> <a id="4133" class="Symbol">:</a> <a id="4135" class="Symbol">(</a><a id="4136" href="Algebras.Products.html#4136" class="Bound">𝒦</a> <a id="4138" class="Symbol">:</a> <a id="4140" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="4145" class="Symbol">(</a><a id="4146" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4154" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="4156" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4157" class="Symbol">)(</a><a id="4159" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="4162" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="4163" class="Symbol">))</a> <a id="4166" class="Symbol">→</a> <a id="4168" href="Algebras.Products.html#2901" class="Function">ℑ</a> <a id="4170" href="Algebras.Products.html#4136" class="Bound">𝒦</a> <a id="4172" class="Symbol">→</a> <a id="4174" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4182" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="4184" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4188" href="Algebras.Products.html#4131" class="Function">𝔄</a> <a id="4190" href="Algebras.Products.html#4190" class="Bound">𝒦</a> <a id="4192" class="Symbol">=</a> <a id="4194" class="Symbol">λ</a> <a id="4196" class="Symbol">(</a><a id="4197" href="Algebras.Products.html#4197" class="Bound">i</a> <a id="4199" class="Symbol">:</a> <a id="4201" class="Symbol">(</a><a id="4202" href="Algebras.Products.html#2901" class="Function">ℑ</a> <a id="4204" href="Algebras.Products.html#4190" class="Bound">𝒦</a><a id="4205" class="Symbol">))</a> <a id="4208" class="Symbol">→</a> <a id="4210" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4212" href="Algebras.Products.html#4197" class="Bound">i</a> <a id="4214" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="4330" href="Algebras.Products.html#4330" class="Function">class-product</a> <a id="4344" class="Symbol">:</a> <a id="4346" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="4351" class="Symbol">(</a><a id="4352" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4360" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="4362" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4363" class="Symbol">)(</a><a id="4365" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="4368" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="4369" class="Symbol">)</a> <a id="4371" class="Symbol">→</a> <a id="4373" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4381" class="Symbol">(</a><a id="4382" href="Algebras.Products.html#2870" class="Bound">𝓧</a> <a id="4384" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4386" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="4389" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="4390" class="Symbol">)</a> <a id="4392" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4396" href="Algebras.Products.html#4330" class="Function">class-product</a> <a id="4410" href="Algebras.Products.html#4410" class="Bound">𝒦</a> <a id="4412" class="Symbol">=</a> <a id="4414" href="Algebras.Products.html#952" class="Function">⨅</a> <a id="4416" class="Symbol">(</a> <a id="4418" href="Algebras.Products.html#4131" class="Function">𝔄</a> <a id="4420" href="Algebras.Products.html#4410" class="Bound">𝒦</a> <a id="4422" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4562" href="Algebras.Products.html#4562" class="Function">class-product&#39;</a> <a id="4577" class="Symbol">:</a> <a id="4579" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="4584" class="Symbol">(</a><a id="4585" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4593" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="4595" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4596" class="Symbol">)(</a><a id="4598" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="4601" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="4602" class="Symbol">)</a> <a id="4604" class="Symbol">→</a> <a id="4606" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4614" class="Symbol">(</a><a id="4615" href="Algebras.Products.html#2870" class="Bound">𝓧</a> <a id="4617" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4619" href="Algebras.Products.html#2026" class="Function">ov</a> <a id="4622" href="Algebras.Products.html#2868" class="Bound">𝓤</a><a id="4623" class="Symbol">)</a> <a id="4625" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4629" href="Algebras.Products.html#4562" class="Function">class-product&#39;</a> <a id="4644" href="Algebras.Products.html#4644" class="Bound">𝒦</a> <a id="4646" class="Symbol">=</a> <a id="4648" href="Algebras.Products.html#952" class="Function">⨅</a> <a id="4650" class="Symbol">λ</a> <a id="4652" class="Symbol">(</a><a id="4653" href="Algebras.Products.html#4653" class="Bound">i</a> <a id="4655" class="Symbol">:</a> <a id="4657" class="Symbol">(</a><a id="4658" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4660" href="Algebras.Products.html#4660" class="Bound">𝑨</a> <a id="4662" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4664" class="Symbol">(</a><a id="4665" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4673" href="Algebras.Products.html#2868" class="Bound">𝓤</a> <a id="4675" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4676" class="Symbol">)</a> <a id="4678" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4680" class="Symbol">(</a><a id="4681" href="Algebras.Products.html#4660" class="Bound">𝑨</a> <a id="4683" href="Relations.Discrete.html#2499" class="Function Operator">∈</a> <a id="4685" href="Algebras.Products.html#4644" class="Bound">𝒦</a><a id="4686" class="Symbol">)</a> <a id="4688" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4690" class="Symbol">(</a><a id="4691" href="Algebras.Products.html#2884" class="Bound">X</a> <a id="4693" class="Symbol">→</a> <a id="4695" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4697" href="Algebras.Products.html#4660" class="Bound">𝑨</a> <a id="4699" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="4700" class="Symbol">)))</a> <a id="4704" class="Symbol">→</a> <a id="4706" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="4708" href="Algebras.Products.html#4653" class="Bound">i</a> <a id="4710" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
