---
layout: default
title : UALib.Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This section presents the [UALib.Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="593" class="Symbol">{-#</a> <a id="597" class="Keyword">OPTIONS</a> <a id="605" class="Pragma">--without-K</a> <a id="617" class="Pragma">--exact-split</a> <a id="631" class="Pragma">--safe</a> <a id="638" class="Symbol">#-}</a>

<a id="643" class="Keyword">open</a> <a id="648" class="Keyword">import</a> <a id="655" href="UALib.Algebras.Signatures.html" class="Module">UALib.Algebras.Signatures</a> <a id="681" class="Keyword">using</a> <a id="687" class="Symbol">(</a><a id="688" href="UALib.Algebras.Signatures.html#1377" class="Function">Signature</a><a id="697" class="Symbol">;</a> <a id="699" href="universes.html#613" class="Generalizable">𝓞</a><a id="700" class="Symbol">;</a> <a id="702" href="universes.html#617" class="Generalizable">𝓥</a><a id="703" class="Symbol">)</a>

<a id="706" class="Keyword">module</a> <a id="713" href="UALib.Algebras.Products.html" class="Module">UALib.Algebras.Products</a> <a id="737" class="Symbol">{</a><a id="738" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a> <a id="740" class="Symbol">:</a> <a id="742" href="UALib.Algebras.Signatures.html#1377" class="Function">Signature</a> <a id="752" href="universes.html#613" class="Generalizable">𝓞</a> <a id="754" href="universes.html#617" class="Generalizable">𝓥</a><a id="755" class="Symbol">}</a> <a id="757" class="Keyword">where</a>

<a id="764" class="Keyword">open</a> <a id="769" class="Keyword">import</a> <a id="776" href="UALib.Algebras.Algebras.html" class="Module">UALib.Algebras.Algebras</a> <a id="800" class="Keyword">hiding</a> <a id="807" class="Symbol">(</a><a id="808" href="universes.html#613" class="Generalizable">𝓞</a><a id="809" class="Symbol">;</a> <a id="811" href="universes.html#617" class="Generalizable">𝓥</a><a id="812" class="Symbol">)</a> <a id="814" class="Keyword">public</a>

</pre>

The product of 𝑆-algebras for the Sigma type representation is defined as follows.

<pre class="Agda">

<a id="⨅"></a><a id="932" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="934" class="Symbol">:</a> <a id="936" class="Symbol">{</a><a id="937" href="UALib.Algebras.Products.html#937" class="Bound">𝓤</a> <a id="939" href="UALib.Algebras.Products.html#939" class="Bound">𝓘</a> <a id="941" class="Symbol">:</a> <a id="943" href="universes.html#551" class="Postulate">Universe</a><a id="951" class="Symbol">}{</a><a id="953" href="UALib.Algebras.Products.html#953" class="Bound">I</a> <a id="955" class="Symbol">:</a> <a id="957" href="UALib.Algebras.Products.html#939" class="Bound">𝓘</a> <a id="959" href="universes.html#758" class="Function Operator">̇</a> <a id="961" class="Symbol">}(</a><a id="963" href="UALib.Algebras.Products.html#963" class="Bound">𝒜</a> <a id="965" class="Symbol">:</a> <a id="967" href="UALib.Algebras.Products.html#953" class="Bound">I</a> <a id="969" class="Symbol">→</a> <a id="971" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="979" href="UALib.Algebras.Products.html#937" class="Bound">𝓤</a> <a id="981" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a> <a id="983" class="Symbol">)</a> <a id="985" class="Symbol">→</a> <a id="987" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="995" class="Symbol">(</a><a id="996" href="UALib.Algebras.Products.html#939" class="Bound">𝓘</a> <a id="998" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1000" href="UALib.Algebras.Products.html#937" class="Bound">𝓤</a><a id="1001" class="Symbol">)</a> <a id="1003" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

<a id="1006" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="1008" href="UALib.Algebras.Products.html#1008" class="Bound">𝒜</a> <a id="1010" class="Symbol">=</a> <a id="1012" class="Symbol">(∀</a> <a id="1015" href="UALib.Algebras.Products.html#1015" class="Bound">i</a> <a id="1017" class="Symbol">→</a> <a id="1019" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="1021" href="UALib.Algebras.Products.html#1008" class="Bound">𝒜</a> <a id="1023" href="UALib.Algebras.Products.html#1015" class="Bound">i</a> <a id="1025" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a><a id="1026" class="Symbol">)</a> <a id="1028" href="UALib.Prelude.Preliminaries.html#5665" class="InductiveConstructor Operator">,</a>                <a id="1045" class="Comment">-- domain of the product algebra</a>

       <a id="1086" class="Symbol">λ</a> <a id="1088" href="UALib.Algebras.Products.html#1088" class="Bound">𝑓</a> <a id="1090" href="UALib.Algebras.Products.html#1090" class="Bound">𝑎</a> <a id="1092" href="UALib.Algebras.Products.html#1092" class="Bound">i</a> <a id="1094" class="Symbol">→</a> <a id="1096" class="Symbol">(</a><a id="1097" href="UALib.Algebras.Products.html#1088" class="Bound">𝑓</a> <a id="1099" href="UALib.Algebras.Algebras.html#2921" class="Function Operator">̂</a> <a id="1101" href="UALib.Algebras.Products.html#1008" class="Bound">𝒜</a> <a id="1103" href="UALib.Algebras.Products.html#1092" class="Bound">i</a><a id="1104" class="Symbol">)</a> <a id="1106" class="Symbol">λ</a> <a id="1108" href="UALib.Algebras.Products.html#1108" class="Bound">x</a> <a id="1110" class="Symbol">→</a> <a id="1112" href="UALib.Algebras.Products.html#1090" class="Bound">𝑎</a> <a id="1114" href="UALib.Algebras.Products.html#1108" class="Bound">x</a> <a id="1116" href="UALib.Algebras.Products.html#1092" class="Bound">i</a>  <a id="1119" class="Comment">-- basic operations of the product algebra</a>

</pre>

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1402" class="Keyword">open</a> <a id="1407" href="UALib.Algebras.Algebras.html#1927" class="Module">algebra</a>

<a id="1416" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1455" href="UALib.Algebras.Products.html#1455" class="Function">⨅&#39;</a> <a id="1458" class="Symbol">:</a> <a id="1460" class="Symbol">{</a><a id="1461" href="UALib.Algebras.Products.html#1461" class="Bound">𝓤</a> <a id="1463" href="UALib.Algebras.Products.html#1463" class="Bound">𝓘</a> <a id="1465" class="Symbol">:</a> <a id="1467" href="universes.html#551" class="Postulate">Universe</a><a id="1475" class="Symbol">}{</a><a id="1477" href="UALib.Algebras.Products.html#1477" class="Bound">I</a> <a id="1479" class="Symbol">:</a> <a id="1481" href="UALib.Algebras.Products.html#1463" class="Bound">𝓘</a> <a id="1483" href="universes.html#758" class="Function Operator">̇</a> <a id="1485" class="Symbol">}(</a><a id="1487" href="UALib.Algebras.Products.html#1487" class="Bound">𝒜</a> <a id="1489" class="Symbol">:</a> <a id="1491" href="UALib.Algebras.Products.html#1477" class="Bound">I</a> <a id="1493" class="Symbol">→</a> <a id="1495" href="UALib.Algebras.Algebras.html#1927" class="Record">algebra</a> <a id="1503" href="UALib.Algebras.Products.html#1461" class="Bound">𝓤</a> <a id="1505" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="1506" class="Symbol">)</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="UALib.Algebras.Algebras.html#1927" class="Record">algebra</a> <a id="1518" class="Symbol">(</a><a id="1519" href="UALib.Algebras.Products.html#1463" class="Bound">𝓘</a> <a id="1521" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1523" href="UALib.Algebras.Products.html#1461" class="Bound">𝓤</a><a id="1524" class="Symbol">)</a> <a id="1526" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

<a id="1529" href="UALib.Algebras.Products.html#1455" class="Function">⨅&#39;</a> <a id="1532" href="UALib.Algebras.Products.html#1532" class="Bound">𝒜</a> <a id="1534" class="Symbol">=</a> <a id="1536" class="Keyword">record</a> <a id="1543" class="Symbol">{</a> <a id="1545" href="UALib.Algebras.Algebras.html#2025" class="Field">univ</a> <a id="1550" class="Symbol">=</a> <a id="1552" class="Symbol">∀</a> <a id="1554" href="UALib.Algebras.Products.html#1554" class="Bound">i</a> <a id="1556" class="Symbol">→</a> <a id="1558" href="UALib.Algebras.Algebras.html#2025" class="Field">univ</a> <a id="1563" class="Symbol">(</a><a id="1564" href="UALib.Algebras.Products.html#1532" class="Bound">𝒜</a> <a id="1566" href="UALib.Algebras.Products.html#1554" class="Bound">i</a><a id="1567" class="Symbol">)</a>               <a id="1583" class="Comment">-- domain</a>
               <a id="1608" class="Symbol">;</a> <a id="1610" href="UALib.Algebras.Algebras.html#2039" class="Field">op</a> <a id="1613" class="Symbol">=</a> <a id="1615" class="Symbol">λ</a> <a id="1617" href="UALib.Algebras.Products.html#1617" class="Bound">𝑓</a> <a id="1619" href="UALib.Algebras.Products.html#1619" class="Bound">𝑎</a> <a id="1621" href="UALib.Algebras.Products.html#1621" class="Bound">i</a> <a id="1623" class="Symbol">→</a> <a id="1625" class="Symbol">(</a><a id="1626" href="UALib.Algebras.Algebras.html#2039" class="Field">op</a> <a id="1629" class="Symbol">(</a><a id="1630" href="UALib.Algebras.Products.html#1532" class="Bound">𝒜</a> <a id="1632" href="UALib.Algebras.Products.html#1621" class="Bound">i</a><a id="1633" class="Symbol">))</a> <a id="1636" href="UALib.Algebras.Products.html#1617" class="Bound">𝑓</a> <a id="1638" class="Symbol">λ</a> <a id="1640" href="UALib.Algebras.Products.html#1640" class="Bound">x</a> <a id="1642" class="Symbol">→</a> <a id="1644" href="UALib.Algebras.Products.html#1619" class="Bound">𝑎</a> <a id="1646" href="UALib.Algebras.Products.html#1640" class="Bound">x</a> <a id="1648" href="UALib.Algebras.Products.html#1621" class="Bound">i</a> <a id="1650" class="Comment">-- basic operations</a>
               <a id="1685" class="Symbol">}</a>

</pre>



#### <a id="notation">Notation</a>

Before we define the type of congruences, we define some syntactic sugar that will be used from now on throughout the [UALib][].

The type `Algebra 𝓤 𝑆` itself has a type; it is `(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ̇` &nbsp;. This type appears quite often throughout the [UALib][], so it is worthwhile to define the following shorthand for its universe level.

<pre class="Agda">

<a id="ov"></a><a id="2091" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="2094" class="Symbol">:</a> <a id="2096" href="universes.html#551" class="Postulate">Universe</a> <a id="2105" class="Symbol">→</a> <a id="2107" href="universes.html#551" class="Postulate">Universe</a>
<a id="2116" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="2119" href="UALib.Algebras.Products.html#2119" class="Bound">𝓤</a> <a id="2121" class="Symbol">=</a> <a id="2123" href="UALib.Algebras.Products.html#752" class="Bound">𝓞</a> <a id="2125" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2127" href="UALib.Algebras.Products.html#754" class="Bound">𝓥</a> <a id="2129" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2131" href="UALib.Algebras.Products.html#2119" class="Bound">𝓤</a> <a id="2133" href="universes.html#527" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">
<a id="2922" class="Keyword">module</a> <a id="2929" href="UALib.Algebras.Products.html#2929" class="Module">_</a> <a id="2931" class="Symbol">{</a><a id="2932" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="2934" href="UALib.Algebras.Products.html#2934" class="Bound">𝓧</a> <a id="2936" class="Symbol">:</a> <a id="2938" href="universes.html#551" class="Postulate">Universe</a><a id="2946" class="Symbol">}{</a><a id="2948" href="UALib.Algebras.Products.html#2948" class="Bound">X</a> <a id="2950" class="Symbol">:</a> <a id="2952" href="UALib.Algebras.Products.html#2934" class="Bound">𝓧</a> <a id="2954" href="universes.html#758" class="Function Operator">̇</a><a id="2955" class="Symbol">}</a> <a id="2957" class="Keyword">where</a>

 <a id="2965" href="UALib.Algebras.Products.html#2965" class="Function">ℑ</a> <a id="2967" class="Symbol">:</a> <a id="2969" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="2974" class="Symbol">(</a><a id="2975" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="2983" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="2985" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="2986" class="Symbol">)(</a><a id="2988" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="2991" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="2992" class="Symbol">)</a> <a id="2994" class="Symbol">→</a> <a id="2996" class="Symbol">(</a><a id="2997" href="UALib.Algebras.Products.html#2934" class="Bound">𝓧</a> <a id="2999" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3001" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="3004" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="3005" class="Symbol">)</a> <a id="3007" href="universes.html#758" class="Function Operator">̇</a>

 <a id="3011" href="UALib.Algebras.Products.html#2965" class="Function">ℑ</a> <a id="3013" href="UALib.Algebras.Products.html#3013" class="Bound">𝒦</a> <a id="3015" class="Symbol">=</a> <a id="3017" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3019" href="UALib.Algebras.Products.html#3019" class="Bound">𝑨</a> <a id="3021" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3023" class="Symbol">(</a><a id="3024" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="3032" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="3034" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="3035" class="Symbol">)</a> <a id="3037" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3039" class="Symbol">(</a><a id="3040" href="UALib.Algebras.Products.html#3019" class="Bound">𝑨</a> <a id="3042" href="UALib.Relations.Unary.html#2732" class="Function Operator">∈</a> <a id="3044" href="UALib.Algebras.Products.html#3013" class="Bound">𝒦</a><a id="3045" class="Symbol">)</a> <a id="3047" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="3049" class="Symbol">(</a><a id="3050" href="UALib.Algebras.Products.html#2948" class="Bound">X</a> <a id="3052" class="Symbol">→</a> <a id="3054" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="3056" href="UALib.Algebras.Products.html#3019" class="Bound">𝑨</a> <a id="3058" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a><a id="3059" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context and we want to keep the context completely general.  Including this context map in the index type ℑ accomplishes this.

Taking the product over the index type ℑ requires a function that takes an index `i : ℑ` and returns the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="3910" href="UALib.Algebras.Products.html#3910" class="Function">𝔄</a> <a id="3912" class="Symbol">:</a> <a id="3914" class="Symbol">(</a><a id="3915" href="UALib.Algebras.Products.html#3915" class="Bound">𝒦</a> <a id="3917" class="Symbol">:</a> <a id="3919" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="3924" class="Symbol">(</a><a id="3925" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="3933" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="3935" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="3936" class="Symbol">)(</a><a id="3938" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="3941" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="3942" class="Symbol">))</a> <a id="3945" class="Symbol">→</a> <a id="3947" href="UALib.Algebras.Products.html#2965" class="Function">ℑ</a> <a id="3949" href="UALib.Algebras.Products.html#3915" class="Bound">𝒦</a> <a id="3951" class="Symbol">→</a> <a id="3953" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="3961" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="3963" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="3967" href="UALib.Algebras.Products.html#3910" class="Function">𝔄</a> <a id="3969" href="UALib.Algebras.Products.html#3969" class="Bound">𝒦</a> <a id="3971" class="Symbol">=</a> <a id="3973" class="Symbol">λ</a> <a id="3975" class="Symbol">(</a><a id="3976" href="UALib.Algebras.Products.html#3976" class="Bound">i</a> <a id="3978" class="Symbol">:</a> <a id="3980" class="Symbol">(</a><a id="3981" href="UALib.Algebras.Products.html#2965" class="Function">ℑ</a> <a id="3983" href="UALib.Algebras.Products.html#3969" class="Bound">𝒦</a><a id="3984" class="Symbol">))</a> <a id="3987" class="Symbol">→</a> <a id="3989" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="3991" href="UALib.Algebras.Products.html#3976" class="Bound">i</a> <a id="3993" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="4109" href="UALib.Algebras.Products.html#4109" class="Function">class-product</a> <a id="4123" class="Symbol">:</a> <a id="4125" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="4130" class="Symbol">(</a><a id="4131" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4139" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="4141" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4142" class="Symbol">)(</a><a id="4144" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="4147" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="4148" class="Symbol">)</a> <a id="4150" class="Symbol">→</a> <a id="4152" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4160" class="Symbol">(</a><a id="4161" href="UALib.Algebras.Products.html#2934" class="Bound">𝓧</a> <a id="4163" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4165" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="4168" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="4169" class="Symbol">)</a> <a id="4171" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="4175" href="UALib.Algebras.Products.html#4109" class="Function">class-product</a> <a id="4189" href="UALib.Algebras.Products.html#4189" class="Bound">𝒦</a> <a id="4191" class="Symbol">=</a> <a id="4193" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="4195" class="Symbol">(</a> <a id="4197" href="UALib.Algebras.Products.html#3910" class="Function">𝔄</a> <a id="4199" href="UALib.Algebras.Products.html#4189" class="Bound">𝒦</a> <a id="4201" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4341" href="UALib.Algebras.Products.html#4341" class="Function">class-product&#39;</a> <a id="4356" class="Symbol">:</a> <a id="4358" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="4363" class="Symbol">(</a><a id="4364" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4372" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="4374" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4375" class="Symbol">)(</a><a id="4377" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="4380" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="4381" class="Symbol">)</a> <a id="4383" class="Symbol">→</a> <a id="4385" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4393" class="Symbol">(</a><a id="4394" href="UALib.Algebras.Products.html#2934" class="Bound">𝓧</a> <a id="4396" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4398" href="UALib.Algebras.Products.html#2091" class="Function">ov</a> <a id="4401" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a><a id="4402" class="Symbol">)</a> <a id="4404" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="4408" href="UALib.Algebras.Products.html#4341" class="Function">class-product&#39;</a> <a id="4423" href="UALib.Algebras.Products.html#4423" class="Bound">𝒦</a> <a id="4425" class="Symbol">=</a> <a id="4427" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="4429" class="Symbol">λ</a> <a id="4431" class="Symbol">(</a><a id="4432" href="UALib.Algebras.Products.html#4432" class="Bound">i</a> <a id="4434" class="Symbol">:</a> <a id="4436" class="Symbol">(</a><a id="4437" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4439" href="UALib.Algebras.Products.html#4439" class="Bound">𝑨</a> <a id="4441" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4443" class="Symbol">(</a><a id="4444" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4452" href="UALib.Algebras.Products.html#2932" class="Bound">𝓤</a> <a id="4454" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4455" class="Symbol">)</a> <a id="4457" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4459" class="Symbol">(</a><a id="4460" href="UALib.Algebras.Products.html#4439" class="Bound">𝑨</a> <a id="4462" href="UALib.Relations.Unary.html#2732" class="Function Operator">∈</a> <a id="4464" href="UALib.Algebras.Products.html#4423" class="Bound">𝒦</a><a id="4465" class="Symbol">)</a> <a id="4467" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4469" class="Symbol">(</a><a id="4470" href="UALib.Algebras.Products.html#2948" class="Bound">X</a> <a id="4472" class="Symbol">→</a> <a id="4474" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="4476" href="UALib.Algebras.Products.html#4439" class="Bound">𝑨</a> <a id="4478" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a><a id="4479" class="Symbol">)))</a> <a id="4483" class="Symbol">→</a> <a id="4485" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="4487" href="UALib.Algebras.Products.html#4432" class="Bound">i</a> <a id="4489" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← UALib.Algebras.Algebras](UALib.Algebras.Algebras.html)
<span style="float:right;">[UALib.Algebras.Congruences →](UALib.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
