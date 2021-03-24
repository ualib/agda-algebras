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

<a id="637" class="Keyword">open</a> <a id="642" class="Keyword">import</a> <a id="649" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="669" class="Keyword">using</a> <a id="675" class="Symbol">(</a><a id="676" href="Algebras.Signatures.html#1251" class="Function">Signature</a><a id="685" class="Symbol">;</a> <a id="687" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="688" class="Symbol">;</a> <a id="690" href="Universes.html#262" class="Generalizable">𝓥</a><a id="691" class="Symbol">)</a>

<a id="694" class="Keyword">module</a> <a id="701" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="719" class="Symbol">{</a><a id="720" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="722" class="Symbol">:</a> <a id="724" href="Algebras.Signatures.html#1251" class="Function">Signature</a> <a id="734" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a> <a id="736" href="Universes.html#262" class="Generalizable">𝓥</a><a id="737" class="Symbol">}</a> <a id="739" class="Keyword">where</a>

<a id="746" class="Keyword">open</a> <a id="751" class="Keyword">import</a> <a id="758" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="776" class="Keyword">hiding</a> <a id="783" class="Symbol">(</a><a id="784" href="Prelude.Preliminaries.html#6856" class="Generalizable">𝓞</a><a id="785" class="Symbol">;</a> <a id="787" href="Universes.html#262" class="Generalizable">𝓥</a><a id="788" class="Symbol">)</a> <a id="790" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a \defn{product of} \ab 𝑆-\defn{algebras} is represented by the following type.

<pre class="Agda">

<a id="1135" class="Keyword">module</a> <a id="1142" href="Algebras.Products.html#1142" class="Module">_</a> <a id="1144" class="Symbol">{</a><a id="1145" href="Algebras.Products.html#1145" class="Bound">𝓤</a> <a id="1147" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1149" class="Symbol">:</a> <a id="1151" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1159" class="Symbol">}{</a><a id="1161" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1163" class="Symbol">:</a> <a id="1165" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1167" href="Universes.html#403" class="Function Operator">̇</a> <a id="1169" class="Symbol">}</a> <a id="1171" class="Keyword">where</a>

 <a id="1179" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="1181" class="Symbol">:</a> <a id="1183" class="Symbol">(</a><a id="1184" href="Algebras.Products.html#1184" class="Bound">𝒜</a> <a id="1186" class="Symbol">:</a> <a id="1188" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1190" class="Symbol">→</a> <a id="1192" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1200" href="Algebras.Products.html#1145" class="Bound">𝓤</a> <a id="1202" href="Algebras.Products.html#720" class="Bound">𝑆</a> <a id="1204" class="Symbol">)</a> <a id="1206" class="Symbol">→</a> <a id="1208" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1216" class="Symbol">(</a><a id="1217" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1219" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1221" href="Algebras.Products.html#1145" class="Bound">𝓤</a><a id="1222" class="Symbol">)</a> <a id="1224" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="1228" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="1230" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1232" class="Symbol">=</a> <a id="1234" class="Symbol">(</a><a id="1235" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1237" href="Algebras.Products.html#1237" class="Bound">i</a> <a id="1239" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1241" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1243" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1245" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="1247" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1249" href="Algebras.Products.html#1237" class="Bound">i</a> <a id="1251" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a><a id="1252" class="Symbol">)</a> <a id="1254" href="Prelude.Preliminaries.html#11707" class="InductiveConstructor Operator">,</a>            <a id="1267" class="Comment">-- domain of the product algebra</a>
       <a id="1307" class="Symbol">λ</a> <a id="1309" href="Algebras.Products.html#1309" class="Bound">𝑓</a> <a id="1311" href="Algebras.Products.html#1311" class="Bound">𝑎</a> <a id="1313" href="Algebras.Products.html#1313" class="Bound">i</a> <a id="1315" class="Symbol">→</a> <a id="1317" class="Symbol">(</a><a id="1318" href="Algebras.Products.html#1309" class="Bound">𝑓</a> <a id="1320" href="Algebras.Algebras.html#2987" class="Function Operator">̂</a> <a id="1322" href="Algebras.Products.html#1230" class="Bound">𝒜</a> <a id="1324" href="Algebras.Products.html#1313" class="Bound">i</a><a id="1325" class="Symbol">)</a> <a id="1327" class="Symbol">λ</a> <a id="1329" href="Algebras.Products.html#1329" class="Bound">x</a> <a id="1331" class="Symbol">→</a> <a id="1333" href="Algebras.Products.html#1311" class="Bound">𝑎</a> <a id="1335" href="Algebras.Products.html#1329" class="Bound">x</a> <a id="1337" href="Algebras.Products.html#1313" class="Bound">i</a>   <a id="1341" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

 <a id="1816" class="Keyword">open</a> <a id="1821" href="Algebras.Algebras.html#1863" class="Module">algebra</a>

 <a id="1831" href="Algebras.Products.html#1831" class="Function">⨅&#39;</a> <a id="1834" class="Symbol">:</a> <a id="1836" class="Symbol">(</a><a id="1837" href="Algebras.Products.html#1837" class="Bound">𝒜</a> <a id="1839" class="Symbol">:</a> <a id="1841" href="Algebras.Products.html#1161" class="Bound">I</a> <a id="1843" class="Symbol">→</a> <a id="1845" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="1853" href="Algebras.Products.html#1145" class="Bound">𝓤</a> <a id="1855" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="1856" class="Symbol">)</a> <a id="1858" class="Symbol">→</a> <a id="1860" href="Algebras.Algebras.html#1863" class="Record">algebra</a> <a id="1868" class="Symbol">(</a><a id="1869" href="Algebras.Products.html#1147" class="Bound">𝓘</a> <a id="1871" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1873" href="Algebras.Products.html#1145" class="Bound">𝓤</a><a id="1874" class="Symbol">)</a> <a id="1876" href="Algebras.Products.html#720" class="Bound">𝑆</a>

 <a id="1880" href="Algebras.Products.html#1831" class="Function">⨅&#39;</a> <a id="1883" href="Algebras.Products.html#1883" class="Bound">𝒜</a> <a id="1885" class="Symbol">=</a> <a id="1887" class="Keyword">record</a> <a id="1894" class="Symbol">{</a> <a id="1896" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="1901" class="Symbol">=</a> <a id="1903" class="Symbol">∀</a> <a id="1905" href="Algebras.Products.html#1905" class="Bound">i</a> <a id="1907" class="Symbol">→</a> <a id="1909" href="Algebras.Algebras.html#1958" class="Field">univ</a> <a id="1914" class="Symbol">(</a><a id="1915" href="Algebras.Products.html#1883" class="Bound">𝒜</a> <a id="1917" href="Algebras.Products.html#1905" class="Bound">i</a><a id="1918" class="Symbol">)</a> <a id="1920" class="Symbol">;</a>                 <a id="1938" class="Comment">-- domain</a>
                 <a id="1965" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="1968" class="Symbol">=</a> <a id="1970" class="Symbol">λ</a> <a id="1972" href="Algebras.Products.html#1972" class="Bound">𝑓</a> <a id="1974" href="Algebras.Products.html#1974" class="Bound">𝑎</a> <a id="1976" href="Algebras.Products.html#1976" class="Bound">i</a> <a id="1978" class="Symbol">→</a> <a id="1980" class="Symbol">(</a><a id="1981" href="Algebras.Algebras.html#1971" class="Field">op</a> <a id="1984" class="Symbol">(</a><a id="1985" href="Algebras.Products.html#1883" class="Bound">𝒜</a> <a id="1987" href="Algebras.Products.html#1976" class="Bound">i</a><a id="1988" class="Symbol">))</a> <a id="1991" href="Algebras.Products.html#1972" class="Bound">𝑓</a> <a id="1993" class="Symbol">λ</a> <a id="1995" href="Algebras.Products.html#1995" class="Bound">x</a> <a id="1997" class="Symbol">→</a> <a id="1999" href="Algebras.Products.html#1974" class="Bound">𝑎</a> <a id="2001" href="Algebras.Products.html#1995" class="Bound">x</a> <a id="2003" href="Algebras.Products.html#1976" class="Bound">i</a> <a id="2005" class="Symbol">}</a> <a id="2007" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2282" href="Algebras.Products.html#2282" class="Function">ov</a> <a id="2285" class="Symbol">:</a> <a id="2287" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2296" class="Symbol">→</a> <a id="2298" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2307" href="Algebras.Products.html#2282" class="Function">ov</a> <a id="2310" href="Algebras.Products.html#2310" class="Bound">𝓤</a> <a id="2312" class="Symbol">=</a> <a id="2314" href="Algebras.Products.html#734" class="Bound">𝓞</a> <a id="2316" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2318" href="Algebras.Products.html#736" class="Bound">𝓥</a> <a id="2320" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2322" href="Algebras.Products.html#2310" class="Bound">𝓤</a> <a id="2324" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) \_`.<sup>[1](Algebras.Products.html#fn1)</sup>

Later we will formally state and prove that, given an arbitrary class `𝒦` of algebras, the product of all subalgebras of algebras in the class belongs to the class  `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise. In fact, it is not immediately clear (to this author, at least) how to even express the product of an entire class of algebras as a dependent type. However, after some concerted thought and an honest reckoning with earlier failed attempts, the right type reveals itself.<sup>[2](Algebras.Products.html#fn2)</sup>

The solution is the \af{class-product} type whose construction is the main goal of this section. To begin, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">

<a id="3463" class="Keyword">module</a> <a id="class-products"></a><a id="3470" href="Algebras.Products.html#3470" class="Module">class-products</a> <a id="3485" class="Symbol">{</a><a id="3486" href="Algebras.Products.html#3486" class="Bound">𝓤</a> <a id="3488" class="Symbol">:</a> <a id="3490" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3498" class="Symbol">}</a> <a id="3500" class="Symbol">(</a><a id="3501" href="Algebras.Products.html#3501" class="Bound">𝒦</a> <a id="3503" class="Symbol">:</a> <a id="3505" href="Relations.Discrete.html#1643" class="Function">Pred</a> <a id="3510" class="Symbol">(</a><a id="3511" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3519" href="Algebras.Products.html#3486" class="Bound">𝓤</a> <a id="3521" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3522" class="Symbol">)(</a><a id="3524" href="Algebras.Products.html#2282" class="Function">ov</a> <a id="3527" href="Algebras.Products.html#3486" class="Bound">𝓤</a><a id="3528" class="Symbol">))</a> <a id="3531" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="3539" href="Algebras.Products.html#3539" class="Function">ℑ</a> <a id="3541" class="Symbol">:</a> <a id="3543" href="Algebras.Products.html#2282" class="Function">ov</a> <a id="3546" href="Algebras.Products.html#3486" class="Bound">𝓤</a> <a id="3548" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3551" href="Algebras.Products.html#3539" class="Function">ℑ</a> <a id="3553" class="Symbol">=</a> <a id="3555" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3557" href="Algebras.Products.html#3557" class="Bound">𝑨</a> <a id="3559" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3561" class="Symbol">(</a><a id="3562" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3570" href="Algebras.Products.html#3486" class="Bound">𝓤</a> <a id="3572" href="Algebras.Products.html#720" class="Bound">𝑆</a><a id="3573" class="Symbol">)</a> <a id="3575" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3577" class="Symbol">(</a><a id="3578" href="Algebras.Products.html#3557" class="Bound">𝑨</a> <a id="3580" href="Relations.Discrete.html#2499" class="Function Operator">∈</a> <a id="3582" href="Algebras.Products.html#3501" class="Bound">𝒦</a><a id="3583" class="Symbol">)</a>

</pre>

Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="3930" href="Algebras.Products.html#3930" class="Function">𝔄</a> <a id="3932" class="Symbol">:</a> <a id="3934" href="Algebras.Products.html#3539" class="Function">ℑ</a> <a id="3936" class="Symbol">→</a> <a id="3938" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3946" href="Algebras.Products.html#3486" class="Bound">𝓤</a> <a id="3948" href="Algebras.Products.html#720" class="Bound">𝑆</a>
 <a id="3951" href="Algebras.Products.html#3930" class="Function">𝔄</a> <a id="3953" class="Symbol">=</a> <a id="3955" class="Symbol">λ</a> <a id="3957" class="Symbol">(</a><a id="3958" href="Algebras.Products.html#3958" class="Bound">i</a> <a id="3960" class="Symbol">:</a> <a id="3962" href="Algebras.Products.html#3539" class="Function">ℑ</a><a id="3963" class="Symbol">)</a> <a id="3965" class="Symbol">→</a> <a id="3967" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a> <a id="3969" href="Algebras.Products.html#3958" class="Bound">i</a> <a id="3971" href="Prelude.Preliminaries.html#12403" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="4087" href="Algebras.Products.html#4087" class="Function">class-product</a> <a id="4101" class="Symbol">:</a> <a id="4103" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4111" class="Symbol">(</a><a id="4112" href="Algebras.Products.html#2282" class="Function">ov</a> <a id="4115" href="Algebras.Products.html#3486" class="Bound">𝓤</a><a id="4116" class="Symbol">)</a> <a id="4118" href="Algebras.Products.html#720" class="Bound">𝑆</a>
 <a id="4121" href="Algebras.Products.html#4087" class="Function">class-product</a> <a id="4135" class="Symbol">=</a> <a id="4137" href="Algebras.Products.html#1179" class="Function">⨅</a> <a id="4139" href="Algebras.Products.html#3930" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> The underscore is merely a placeholder for the universe of the predicate type and needn't concern us here.</span>

<sup>2</sup><span class="footnote" id="fn2"> This was our own experience, but readers are encouraged to try to derive for themselves a type that represents the product of all algebras satisfying a given predicate. It is a good exercise. (*Hint*. The answer is not `Π 𝒦`. Although the latter is a valid type, it represnts not the product of algebras in `𝒦`, but rather the assertion that every algebra of type `Algebra 𝓤 𝑆` belongs to `𝒦`.)</span>

<br>
<br>

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

<!--

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

 class-product' : Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
 class-product' 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

-->

