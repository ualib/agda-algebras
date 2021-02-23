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

Before proceeding, we define some convenient syntactic sugar. The type `Algebra 𝓤 𝑆` itself has a type; it is `(𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺) ̇` &nbsp;. This type appears quite often throughout the [UALib][], so it is worthwhile to define the following shorthand for its universe level.

<pre class="Agda">

<a id="ov"></a><a id="2023" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="2026" class="Symbol">:</a> <a id="2028" href="universes.html#551" class="Postulate">Universe</a> <a id="2037" class="Symbol">→</a> <a id="2039" href="universes.html#551" class="Postulate">Universe</a>
<a id="2048" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="2051" href="UALib.Algebras.Products.html#2051" class="Bound">𝓤</a> <a id="2053" class="Symbol">=</a> <a id="2055" href="UALib.Algebras.Products.html#752" class="Bound">𝓞</a> <a id="2057" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2059" href="UALib.Algebras.Products.html#754" class="Bound">𝓥</a> <a id="2061" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2063" href="UALib.Algebras.Products.html#2051" class="Bound">𝓤</a> <a id="2065" href="universes.html#527" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">
<a id="2854" class="Keyword">module</a> <a id="2861" href="UALib.Algebras.Products.html#2861" class="Module">_</a> <a id="2863" class="Symbol">{</a><a id="2864" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="2866" href="UALib.Algebras.Products.html#2866" class="Bound">𝓧</a> <a id="2868" class="Symbol">:</a> <a id="2870" href="universes.html#551" class="Postulate">Universe</a><a id="2878" class="Symbol">}{</a><a id="2880" href="UALib.Algebras.Products.html#2880" class="Bound">X</a> <a id="2882" class="Symbol">:</a> <a id="2884" href="UALib.Algebras.Products.html#2866" class="Bound">𝓧</a> <a id="2886" href="universes.html#758" class="Function Operator">̇</a><a id="2887" class="Symbol">}</a> <a id="2889" class="Keyword">where</a>

 <a id="2897" href="UALib.Algebras.Products.html#2897" class="Function">ℑ</a> <a id="2899" class="Symbol">:</a> <a id="2901" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="2906" class="Symbol">(</a><a id="2907" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="2915" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="2917" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="2918" class="Symbol">)(</a><a id="2920" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="2923" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="2924" class="Symbol">)</a> <a id="2926" class="Symbol">→</a> <a id="2928" class="Symbol">(</a><a id="2929" href="UALib.Algebras.Products.html#2866" class="Bound">𝓧</a> <a id="2931" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2933" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="2936" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="2937" class="Symbol">)</a> <a id="2939" href="universes.html#758" class="Function Operator">̇</a>

 <a id="2943" href="UALib.Algebras.Products.html#2897" class="Function">ℑ</a> <a id="2945" href="UALib.Algebras.Products.html#2945" class="Bound">𝒦</a> <a id="2947" class="Symbol">=</a> <a id="2949" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="2951" href="UALib.Algebras.Products.html#2951" class="Bound">𝑨</a> <a id="2953" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="2955" class="Symbol">(</a><a id="2956" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="2964" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="2966" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="2967" class="Symbol">)</a> <a id="2969" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="2971" class="Symbol">(</a><a id="2972" href="UALib.Algebras.Products.html#2951" class="Bound">𝑨</a> <a id="2974" href="UALib.Relations.Unary.html#2733" class="Function Operator">∈</a> <a id="2976" href="UALib.Algebras.Products.html#2945" class="Bound">𝒦</a><a id="2977" class="Symbol">)</a> <a id="2979" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="2981" class="Symbol">(</a><a id="2982" href="UALib.Algebras.Products.html#2880" class="Bound">X</a> <a id="2984" class="Symbol">→</a> <a id="2986" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="2988" href="UALib.Algebras.Products.html#2951" class="Bound">𝑨</a> <a id="2990" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a><a id="2991" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context and we want to keep the context completely general.  Including this context map in the index type ℑ accomplishes this.

Taking the product over the index type ℑ requires a function that takes an index `i : ℑ` and returns the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="3842" href="UALib.Algebras.Products.html#3842" class="Function">𝔄</a> <a id="3844" class="Symbol">:</a> <a id="3846" class="Symbol">(</a><a id="3847" href="UALib.Algebras.Products.html#3847" class="Bound">𝒦</a> <a id="3849" class="Symbol">:</a> <a id="3851" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="3856" class="Symbol">(</a><a id="3857" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="3865" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="3867" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="3868" class="Symbol">)(</a><a id="3870" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="3873" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="3874" class="Symbol">))</a> <a id="3877" class="Symbol">→</a> <a id="3879" href="UALib.Algebras.Products.html#2897" class="Function">ℑ</a> <a id="3881" href="UALib.Algebras.Products.html#3847" class="Bound">𝒦</a> <a id="3883" class="Symbol">→</a> <a id="3885" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="3893" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="3895" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="3899" href="UALib.Algebras.Products.html#3842" class="Function">𝔄</a> <a id="3901" href="UALib.Algebras.Products.html#3901" class="Bound">𝒦</a> <a id="3903" class="Symbol">=</a> <a id="3905" class="Symbol">λ</a> <a id="3907" class="Symbol">(</a><a id="3908" href="UALib.Algebras.Products.html#3908" class="Bound">i</a> <a id="3910" class="Symbol">:</a> <a id="3912" class="Symbol">(</a><a id="3913" href="UALib.Algebras.Products.html#2897" class="Function">ℑ</a> <a id="3915" href="UALib.Algebras.Products.html#3901" class="Bound">𝒦</a><a id="3916" class="Symbol">))</a> <a id="3919" class="Symbol">→</a> <a id="3921" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="3923" href="UALib.Algebras.Products.html#3908" class="Bound">i</a> <a id="3925" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="4041" href="UALib.Algebras.Products.html#4041" class="Function">class-product</a> <a id="4055" class="Symbol">:</a> <a id="4057" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="4062" class="Symbol">(</a><a id="4063" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4071" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="4073" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4074" class="Symbol">)(</a><a id="4076" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="4079" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="4080" class="Symbol">)</a> <a id="4082" class="Symbol">→</a> <a id="4084" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4092" class="Symbol">(</a><a id="4093" href="UALib.Algebras.Products.html#2866" class="Bound">𝓧</a> <a id="4095" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4097" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="4100" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="4101" class="Symbol">)</a> <a id="4103" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="4107" href="UALib.Algebras.Products.html#4041" class="Function">class-product</a> <a id="4121" href="UALib.Algebras.Products.html#4121" class="Bound">𝒦</a> <a id="4123" class="Symbol">=</a> <a id="4125" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="4127" class="Symbol">(</a> <a id="4129" href="UALib.Algebras.Products.html#3842" class="Function">𝔄</a> <a id="4131" href="UALib.Algebras.Products.html#4121" class="Bound">𝒦</a> <a id="4133" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4273" href="UALib.Algebras.Products.html#4273" class="Function">class-product&#39;</a> <a id="4288" class="Symbol">:</a> <a id="4290" href="UALib.Relations.Unary.html#1071" class="Function">Pred</a> <a id="4295" class="Symbol">(</a><a id="4296" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4304" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="4306" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4307" class="Symbol">)(</a><a id="4309" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="4312" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="4313" class="Symbol">)</a> <a id="4315" class="Symbol">→</a> <a id="4317" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4325" class="Symbol">(</a><a id="4326" href="UALib.Algebras.Products.html#2866" class="Bound">𝓧</a> <a id="4328" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4330" href="UALib.Algebras.Products.html#2023" class="Function">ov</a> <a id="4333" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a><a id="4334" class="Symbol">)</a> <a id="4336" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a>

 <a id="4340" href="UALib.Algebras.Products.html#4273" class="Function">class-product&#39;</a> <a id="4355" href="UALib.Algebras.Products.html#4355" class="Bound">𝒦</a> <a id="4357" class="Symbol">=</a> <a id="4359" href="UALib.Algebras.Products.html#932" class="Function">⨅</a> <a id="4361" class="Symbol">λ</a> <a id="4363" class="Symbol">(</a><a id="4364" href="UALib.Algebras.Products.html#4364" class="Bound">i</a> <a id="4366" class="Symbol">:</a> <a id="4368" class="Symbol">(</a><a id="4369" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4371" href="UALib.Algebras.Products.html#4371" class="Bound">𝑨</a> <a id="4373" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4375" class="Symbol">(</a><a id="4376" href="UALib.Algebras.Algebras.html#771" class="Function">Algebra</a> <a id="4384" href="UALib.Algebras.Products.html#2864" class="Bound">𝓤</a> <a id="4386" href="UALib.Algebras.Products.html#738" class="Bound">𝑆</a><a id="4387" class="Symbol">)</a> <a id="4389" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4391" class="Symbol">(</a><a id="4392" href="UALib.Algebras.Products.html#4371" class="Bound">𝑨</a> <a id="4394" href="UALib.Relations.Unary.html#2733" class="Function Operator">∈</a> <a id="4396" href="UALib.Algebras.Products.html#4355" class="Bound">𝒦</a><a id="4397" class="Symbol">)</a> <a id="4399" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4401" class="Symbol">(</a><a id="4402" href="UALib.Algebras.Products.html#2880" class="Bound">X</a> <a id="4404" class="Symbol">→</a> <a id="4406" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="4408" href="UALib.Algebras.Products.html#4371" class="Bound">𝑨</a> <a id="4410" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a><a id="4411" class="Symbol">)))</a> <a id="4415" class="Symbol">→</a> <a id="4417" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a> <a id="4419" href="UALib.Algebras.Products.html#4364" class="Bound">i</a> <a id="4421" href="UALib.Prelude.Preliminaries.html#11658" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← UALib.Algebras.Algebras](UALib.Algebras.Algebras.html)
<span style="float:right;">[UALib.Algebras.Congruences →](UALib.Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
