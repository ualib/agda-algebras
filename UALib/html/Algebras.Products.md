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

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1299" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#5600" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1299" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#5600" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#5600" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

The product of 𝑆-algebras for the Sigma type representation is defined as follows.

<pre class="Agda">

<a id="⨅"></a><a id="908" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="910" class="Symbol">:</a> <a id="912" class="Symbol">{</a><a id="913" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="915" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="917" class="Symbol">:</a> <a id="919" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="927" class="Symbol">}{</a><a id="929" href="Algebras.Products.html#929" class="Bound">I</a> <a id="931" class="Symbol">:</a> <a id="933" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="935" href="Universes.html#403" class="Function Operator">̇</a> <a id="937" class="Symbol">}(</a><a id="939" href="Algebras.Products.html#939" class="Bound">𝒜</a> <a id="941" class="Symbol">:</a> <a id="943" href="Algebras.Products.html#929" class="Bound">I</a> <a id="945" class="Symbol">→</a> <a id="947" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="955" href="Algebras.Products.html#913" class="Bound">𝓤</a> <a id="957" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="959" class="Symbol">)</a> <a id="961" class="Symbol">→</a> <a id="963" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="971" class="Symbol">(</a><a id="972" href="Algebras.Products.html#915" class="Bound">𝓘</a> <a id="974" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="976" href="Algebras.Products.html#913" class="Bound">𝓤</a><a id="977" class="Symbol">)</a> <a id="979" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="982" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="984" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="986" class="Symbol">=</a> <a id="988" class="Symbol">(∀</a> <a id="991" href="Algebras.Products.html#991" class="Bound">i</a> <a id="993" class="Symbol">→</a> <a id="995" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="997" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="999" href="Algebras.Products.html#991" class="Bound">i</a> <a id="1001" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a><a id="1002" class="Symbol">)</a> <a id="1004" href="Prelude.Preliminaries.html#14564" class="InductiveConstructor Operator">,</a>               <a id="1020" class="Comment">-- domain of the product algebra</a>

       <a id="1061" class="Symbol">λ</a> <a id="1063" href="Algebras.Products.html#1063" class="Bound">𝑓</a> <a id="1065" href="Algebras.Products.html#1065" class="Bound">𝑎</a> <a id="1067" href="Algebras.Products.html#1067" class="Bound">i</a> <a id="1069" class="Symbol">→</a> <a id="1071" class="Symbol">(</a><a id="1072" href="Algebras.Products.html#1063" class="Bound">𝑓</a> <a id="1074" href="Algebras.Algebras.html#2844" class="Function Operator">̂</a> <a id="1076" href="Algebras.Products.html#984" class="Bound">𝒜</a> <a id="1078" href="Algebras.Products.html#1067" class="Bound">i</a><a id="1079" class="Symbol">)</a> <a id="1081" class="Symbol">λ</a> <a id="1083" href="Algebras.Products.html#1083" class="Bound">x</a> <a id="1085" class="Symbol">→</a> <a id="1087" href="Algebras.Products.html#1065" class="Bound">𝑎</a> <a id="1089" href="Algebras.Products.html#1083" class="Bound">x</a> <a id="1091" href="Algebras.Products.html#1067" class="Bound">i</a>  <a id="1094" class="Comment">-- basic operations of the product algebra</a>

</pre>

Other modules of the [UALib][] will use the foregoing product type exclusively.  However, for completeness, we now demonstrate how one would construct product algebras when the factors are defined using records.

<pre class="Agda">

<a id="1377" class="Keyword">open</a> <a id="1382" href="Algebras.Algebras.html#1850" class="Module">algebra</a>

<a id="1391" class="Comment">-- product for algebras of record type</a>
<a id="⨅&#39;"></a><a id="1430" href="Algebras.Products.html#1430" class="Function">⨅&#39;</a> <a id="1433" class="Symbol">:</a> <a id="1435" class="Symbol">{</a><a id="1436" href="Algebras.Products.html#1436" class="Bound">𝓤</a> <a id="1438" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1440" class="Symbol">:</a> <a id="1442" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1450" class="Symbol">}{</a><a id="1452" href="Algebras.Products.html#1452" class="Bound">I</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1458" href="Universes.html#403" class="Function Operator">̇</a> <a id="1460" class="Symbol">}(</a><a id="1462" href="Algebras.Products.html#1462" class="Bound">𝒜</a> <a id="1464" class="Symbol">:</a> <a id="1466" href="Algebras.Products.html#1452" class="Bound">I</a> <a id="1468" class="Symbol">→</a> <a id="1470" href="Algebras.Algebras.html#1850" class="Record">algebra</a> <a id="1478" href="Algebras.Products.html#1436" class="Bound">𝓤</a> <a id="1480" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1481" class="Symbol">)</a> <a id="1483" class="Symbol">→</a> <a id="1485" href="Algebras.Algebras.html#1850" class="Record">algebra</a> <a id="1493" class="Symbol">(</a><a id="1494" href="Algebras.Products.html#1438" class="Bound">𝓘</a> <a id="1496" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1498" href="Algebras.Products.html#1436" class="Bound">𝓤</a><a id="1499" class="Symbol">)</a> <a id="1501" href="Algebras.Products.html#720" class="Bound">𝑆</a>

<a id="1504" href="Algebras.Products.html#1430" class="Function">⨅&#39;</a> <a id="1507" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1509" class="Symbol">=</a> <a id="1511" class="Keyword">record</a> <a id="1518" class="Symbol">{</a> <a id="1520" href="Algebras.Algebras.html#1948" class="Field">univ</a> <a id="1525" class="Symbol">=</a> <a id="1527" class="Symbol">∀</a> <a id="1529" href="Algebras.Products.html#1529" class="Bound">i</a> <a id="1531" class="Symbol">→</a> <a id="1533" href="Algebras.Algebras.html#1948" class="Field">univ</a> <a id="1538" class="Symbol">(</a><a id="1539" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1541" href="Algebras.Products.html#1529" class="Bound">i</a><a id="1542" class="Symbol">)</a>                <a id="1559" class="Comment">-- domain</a>
               <a id="1584" class="Symbol">;</a> <a id="1586" href="Algebras.Algebras.html#1962" class="Field">op</a> <a id="1589" class="Symbol">=</a> <a id="1591" class="Symbol">λ</a> <a id="1593" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1595" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1597" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1599" class="Symbol">→</a> <a id="1601" class="Symbol">(</a><a id="1602" href="Algebras.Algebras.html#1962" class="Field">op</a> <a id="1605" class="Symbol">(</a><a id="1606" href="Algebras.Products.html#1507" class="Bound">𝒜</a> <a id="1608" href="Algebras.Products.html#1597" class="Bound">i</a><a id="1609" class="Symbol">))</a> <a id="1612" href="Algebras.Products.html#1593" class="Bound">𝑓</a> <a id="1614" class="Symbol">λ</a> <a id="1616" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1618" class="Symbol">→</a> <a id="1620" href="Algebras.Products.html#1595" class="Bound">𝑎</a> <a id="1622" href="Algebras.Products.html#1616" class="Bound">x</a> <a id="1624" href="Algebras.Products.html#1597" class="Bound">i</a> <a id="1626" class="Comment">-- basic operations</a>
               <a id="1661" class="Symbol">}</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="1918" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="1932" class="Symbol">→</a> <a id="1934" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="1943" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="1946" href="Algebras.Products.html#1946" class="Bound">𝓤</a> <a id="1948" class="Symbol">=</a> <a id="1950" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="1952" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1954" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="1956" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1958" href="Algebras.Products.html#1946" class="Bound">𝓤</a> <a id="1960" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

Later we will formally state and prove that, given an arbitrary class 𝒦 of algebras, the product of all subalgebras of algebras in the class belongs to SP(𝒦) (subalgebras of products of algebras in 𝒦). That is, ⨅ S(𝒦) ∈ SP(𝒦 ). This turns out to be a nontrivial exercise. In fact, it is not immediately obvious (at least to this author) how one should express the product of an entire class of algebras as a dependent type. After a number of failed attempts, the right type revealed itself in the form of the `class-product` whose construction is the main goal of this section.

First, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">
<a id="2749" class="Keyword">module</a> <a id="2756" href="Algebras.Products.html#2756" class="Module">_</a> <a id="2758" class="Symbol">{</a><a id="2759" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="2761" href="Algebras.Products.html#2761" class="Bound">𝓧</a> <a id="2763" class="Symbol">:</a> <a id="2765" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="2773" class="Symbol">}{</a><a id="2775" href="Algebras.Products.html#2775" class="Bound">X</a> <a id="2777" class="Symbol">:</a> <a id="2779" href="Algebras.Products.html#2761" class="Bound">𝓧</a> <a id="2781" href="Universes.html#403" class="Function Operator">̇</a><a id="2782" class="Symbol">}</a> <a id="2784" class="Keyword">where</a>

 <a id="2792" href="Algebras.Products.html#2792" class="Function">ℑ</a> <a id="2794" class="Symbol">:</a> <a id="2796" href="Relations.Unary.html#959" class="Function">Pred</a> <a id="2801" class="Symbol">(</a><a id="2802" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2810" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="2812" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2813" class="Symbol">)(</a><a id="2815" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="2818" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="2819" class="Symbol">)</a> <a id="2821" class="Symbol">→</a> <a id="2823" class="Symbol">(</a><a id="2824" href="Algebras.Products.html#2761" class="Bound">𝓧</a> <a id="2826" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2828" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="2831" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="2832" class="Symbol">)</a> <a id="2834" href="Universes.html#403" class="Function Operator">̇</a>

 <a id="2838" href="Algebras.Products.html#2792" class="Function">ℑ</a> <a id="2840" href="Algebras.Products.html#2840" class="Bound">𝒦</a> <a id="2842" class="Symbol">=</a> <a id="2844" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="2846" href="Algebras.Products.html#2846" class="Bound">𝑨</a> <a id="2848" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="2850" class="Symbol">(</a><a id="2851" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="2859" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="2861" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="2862" class="Symbol">)</a> <a id="2864" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="2866" class="Symbol">(</a><a id="2867" href="Algebras.Products.html#2846" class="Bound">𝑨</a> <a id="2869" href="Relations.Unary.html#1958" class="Function Operator">∈</a> <a id="2871" href="Algebras.Products.html#2840" class="Bound">𝒦</a><a id="2872" class="Symbol">)</a> <a id="2874" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="2876" class="Symbol">(</a><a id="2877" href="Algebras.Products.html#2775" class="Bound">X</a> <a id="2879" class="Symbol">→</a> <a id="2881" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="2883" href="Algebras.Products.html#2846" class="Bound">𝑨</a> <a id="2885" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a><a id="2886" class="Symbol">)</a>

</pre>

Notice that the second component of this dependent pair type is `(𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣)`.  In previous versions of the [UALib][] this second component was simply `𝑨 ∈ 𝒦`.  However, we realized that adding a mapping of type `X → ∣ 𝑨 ∣` is quite useful.  The reason for this will become clear later; for now, suffice it to say that a map X → ∣ 𝑨 ∣ may be viewed as a context and we want to keep the context completely general.  Including this context map in the index type ℑ accomplishes this.

Taking the product over the index type ℑ requires a function that takes an index `i : ℑ` and returns the corresponding algebra.  Each `i : ℑ` is a triple, say, `(𝑨 , p , h)`, where `𝑨 : Algebra 𝓤 𝑆`, `p : 𝑨 ∈ 𝒦`, and `h : X → ∣ 𝑨 ∣`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="3737" href="Algebras.Products.html#3737" class="Function">𝔄</a> <a id="3739" class="Symbol">:</a> <a id="3741" class="Symbol">(</a><a id="3742" href="Algebras.Products.html#3742" class="Bound">𝒦</a> <a id="3744" class="Symbol">:</a> <a id="3746" href="Relations.Unary.html#959" class="Function">Pred</a> <a id="3751" class="Symbol">(</a><a id="3752" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3760" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="3762" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3763" class="Symbol">)(</a><a id="3765" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="3768" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="3769" class="Symbol">))</a> <a id="3772" class="Symbol">→</a> <a id="3774" href="Algebras.Products.html#2792" class="Function">ℑ</a> <a id="3776" href="Algebras.Products.html#3742" class="Bound">𝒦</a> <a id="3778" class="Symbol">→</a> <a id="3780" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3788" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="3790" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="3794" href="Algebras.Products.html#3737" class="Function">𝔄</a> <a id="3796" href="Algebras.Products.html#3796" class="Bound">𝒦</a> <a id="3798" class="Symbol">=</a> <a id="3800" class="Symbol">λ</a> <a id="3802" class="Symbol">(</a><a id="3803" href="Algebras.Products.html#3803" class="Bound">i</a> <a id="3805" class="Symbol">:</a> <a id="3807" class="Symbol">(</a><a id="3808" href="Algebras.Products.html#2792" class="Function">ℑ</a> <a id="3810" href="Algebras.Products.html#3796" class="Bound">𝒦</a><a id="3811" class="Symbol">))</a> <a id="3814" class="Symbol">→</a> <a id="3816" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="3818" href="Algebras.Products.html#3803" class="Bound">i</a> <a id="3820" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="3936" href="Algebras.Products.html#3936" class="Function">class-product</a> <a id="3950" class="Symbol">:</a> <a id="3952" href="Relations.Unary.html#959" class="Function">Pred</a> <a id="3957" class="Symbol">(</a><a id="3958" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3966" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="3968" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3969" class="Symbol">)(</a><a id="3971" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="3974" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="3975" class="Symbol">)</a> <a id="3977" class="Symbol">→</a> <a id="3979" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="3987" class="Symbol">(</a><a id="3988" href="Algebras.Products.html#2761" class="Bound">𝓧</a> <a id="3990" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="3992" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="3995" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="3996" class="Symbol">)</a> <a id="3998" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4002" href="Algebras.Products.html#3936" class="Function">class-product</a> <a id="4016" href="Algebras.Products.html#4016" class="Bound">𝒦</a> <a id="4018" class="Symbol">=</a> <a id="4020" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4022" class="Symbol">(</a> <a id="4024" href="Algebras.Products.html#3737" class="Function">𝔄</a> <a id="4026" href="Algebras.Products.html#4016" class="Bound">𝒦</a> <a id="4028" class="Symbol">)</a>

</pre>

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

<pre class="Agda">

 <a id="4168" href="Algebras.Products.html#4168" class="Function">class-product&#39;</a> <a id="4183" class="Symbol">:</a> <a id="4185" href="Relations.Unary.html#959" class="Function">Pred</a> <a id="4190" class="Symbol">(</a><a id="4191" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4199" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="4201" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4202" class="Symbol">)(</a><a id="4204" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4207" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="4208" class="Symbol">)</a> <a id="4210" class="Symbol">→</a> <a id="4212" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4220" class="Symbol">(</a><a id="4221" href="Algebras.Products.html#2761" class="Bound">𝓧</a> <a id="4223" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="4225" href="Algebras.Products.html#1918" class="Function">ov</a> <a id="4228" href="Algebras.Products.html#2759" class="Bound">𝓤</a><a id="4229" class="Symbol">)</a> <a id="4231" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="4235" href="Algebras.Products.html#4168" class="Function">class-product&#39;</a> <a id="4250" href="Algebras.Products.html#4250" class="Bound">𝒦</a> <a id="4252" class="Symbol">=</a> <a id="4254" href="Algebras.Products.html#908" class="Function">⨅</a> <a id="4256" class="Symbol">λ</a> <a id="4258" class="Symbol">(</a><a id="4259" href="Algebras.Products.html#4259" class="Bound">i</a> <a id="4261" class="Symbol">:</a> <a id="4263" class="Symbol">(</a><a id="4264" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4266" href="Algebras.Products.html#4266" class="Bound">𝑨</a> <a id="4268" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4270" class="Symbol">(</a><a id="4271" href="Algebras.Algebras.html#694" class="Function">Algebra</a> <a id="4279" href="Algebras.Products.html#2759" class="Bound">𝓤</a> <a id="4281" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="4282" class="Symbol">)</a> <a id="4284" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4286" class="Symbol">(</a><a id="4287" href="Algebras.Products.html#4266" class="Bound">𝑨</a> <a id="4289" href="Relations.Unary.html#1958" class="Function Operator">∈</a> <a id="4291" href="Algebras.Products.html#4250" class="Bound">𝒦</a><a id="4292" class="Symbol">)</a> <a id="4294" href="MGS-MLTT.html#3515" class="Function Operator">×</a> <a id="4296" class="Symbol">(</a><a id="4297" href="Algebras.Products.html#2775" class="Bound">X</a> <a id="4299" class="Symbol">→</a> <a id="4301" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="4303" href="Algebras.Products.html#4266" class="Bound">𝑨</a> <a id="4305" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a><a id="4306" class="Symbol">)))</a> <a id="4310" class="Symbol">→</a> <a id="4312" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a> <a id="4314" href="Algebras.Products.html#4259" class="Bound">i</a> <a id="4316" href="Prelude.Preliminaries.html#13569" class="Function Operator">∣</a>

</pre>

If `p : 𝑨 ∈ 𝒦` and `h : X → ∣ 𝑨 ∣`, then we can think of the triple `(𝑨 , p , h) ∈ ℑ 𝒦` as an index over the class, and so we can think of `𝔄 (𝑨 , p , h)` (which is simply `𝑨`) as the projection of the product `⨅ ( 𝔄 𝒦 )` onto the `(𝑨 , p, h)`-th component.





-----------------------

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}
