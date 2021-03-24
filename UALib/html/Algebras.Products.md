---
layout: default
title : Algebras.Products module (Agda Universal Algebra Library)
date : 2021-01-12
author: William DeMeo
---


### <a id="product-algebras">Product Algebras</a>

This section presents the [Algebras.Products][] module of the [Agda Universal Algebra Library][].

Notice that we begin this module by assuming a signature `𝑆 : Signature 𝓞 𝓥` which is then present and available throughout the module.

**NOTATION**.  From now on, the remaining modules of the [UALib][] will assume universes 𝓞 and 𝓥, and a fixed signature type `𝑆 : Signature 𝓞 𝓥`.

<pre class="Agda">

<a id="581" class="Symbol">{-#</a> <a id="585" class="Keyword">OPTIONS</a> <a id="593" class="Pragma">--without-K</a> <a id="605" class="Pragma">--exact-split</a> <a id="619" class="Pragma">--safe</a> <a id="626" class="Symbol">#-}</a>

<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="Algebras.Signatures.html#1239" class="Function">Signature</a><a id="679" class="Symbol">;</a> <a id="681" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a><a id="682" class="Symbol">;</a> <a id="684" href="Universes.html#262" class="Generalizable">𝓥</a><a id="685" class="Symbol">)</a>

<a id="688" class="Keyword">module</a> <a id="695" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="713" class="Symbol">{</a><a id="714" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="716" class="Symbol">:</a> <a id="718" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="728" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a> <a id="730" href="Universes.html#262" class="Generalizable">𝓥</a><a id="731" class="Symbol">}</a> <a id="733" class="Keyword">where</a>

<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="770" class="Keyword">hiding</a> <a id="777" class="Symbol">(</a><a id="778" href="Overture.Preliminaries.html#6863" class="Generalizable">𝓞</a><a id="779" class="Symbol">;</a> <a id="781" href="Universes.html#262" class="Generalizable">𝓥</a><a id="782" class="Symbol">)</a> <a id="784" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a \defn{product of} \ab 𝑆-\defn{algebras} is represented by the following type.

<pre class="Agda">

<a id="1129" class="Keyword">module</a> <a id="1136" href="Algebras.Products.html#1136" class="Module">_</a> <a id="1138" class="Symbol">{</a><a id="1139" href="Algebras.Products.html#1139" class="Bound">𝓤</a> <a id="1141" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1143" class="Symbol">:</a> <a id="1145" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1153" class="Symbol">}{</a><a id="1155" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1161" href="Universes.html#403" class="Function Operator">̇</a> <a id="1163" class="Symbol">}</a> <a id="1165" class="Keyword">where</a>

 <a id="1173" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="1175" class="Symbol">:</a> <a id="1177" class="Symbol">(</a><a id="1178" href="Algebras.Products.html#1178" class="Bound">𝒜</a> <a id="1180" class="Symbol">:</a> <a id="1182" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1184" class="Symbol">→</a> <a id="1186" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1194" href="Algebras.Products.html#1139" class="Bound">𝓤</a> <a id="1196" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="1198" class="Symbol">)</a> <a id="1200" class="Symbol">→</a> <a id="1202" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1210" class="Symbol">(</a><a id="1211" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1213" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1215" href="Algebras.Products.html#1139" class="Bound">𝓤</a><a id="1216" class="Symbol">)</a> <a id="1218" href="Algebras.Products.html#714" class="Bound">𝑆</a>

 <a id="1222" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="1224" href="Algebras.Products.html#1224" class="Bound">𝒜</a> <a id="1226" class="Symbol">=</a> <a id="1228" class="Symbol">(</a><a id="1229" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1231" href="Algebras.Products.html#1231" class="Bound">i</a> <a id="1233" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1235" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1237" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1239" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="1241" href="Algebras.Products.html#1224" class="Bound">𝒜</a> <a id="1243" href="Algebras.Products.html#1231" class="Bound">i</a> <a id="1245" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a><a id="1246" class="Symbol">)</a> <a id="1248" href="Overture.Preliminaries.html#11717" class="InductiveConstructor Operator">,</a>            <a id="1261" class="Comment">-- domain of the product algebra</a>
       <a id="1301" class="Symbol">λ</a> <a id="1303" href="Algebras.Products.html#1303" class="Bound">𝑓</a> <a id="1305" href="Algebras.Products.html#1305" class="Bound">𝑎</a> <a id="1307" href="Algebras.Products.html#1307" class="Bound">i</a> <a id="1309" class="Symbol">→</a> <a id="1311" class="Symbol">(</a><a id="1312" href="Algebras.Products.html#1303" class="Bound">𝑓</a> <a id="1314" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="1316" href="Algebras.Products.html#1224" class="Bound">𝒜</a> <a id="1318" href="Algebras.Products.html#1307" class="Bound">i</a><a id="1319" class="Symbol">)</a> <a id="1321" class="Symbol">λ</a> <a id="1323" href="Algebras.Products.html#1323" class="Bound">x</a> <a id="1325" class="Symbol">→</a> <a id="1327" href="Algebras.Products.html#1305" class="Bound">𝑎</a> <a id="1329" href="Algebras.Products.html#1323" class="Bound">x</a> <a id="1331" href="Algebras.Products.html#1307" class="Bound">i</a>   <a id="1335" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

 <a id="1810" class="Keyword">open</a> <a id="1815" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="1825" href="Algebras.Products.html#1825" class="Function">⨅&#39;</a> <a id="1828" class="Symbol">:</a> <a id="1830" class="Symbol">(</a><a id="1831" href="Algebras.Products.html#1831" class="Bound">𝒜</a> <a id="1833" class="Symbol">:</a> <a id="1835" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1837" class="Symbol">→</a> <a id="1839" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1847" href="Algebras.Products.html#1139" class="Bound">𝓤</a> <a id="1849" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="1850" class="Symbol">)</a> <a id="1852" class="Symbol">→</a> <a id="1854" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1862" class="Symbol">(</a><a id="1863" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1865" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1867" href="Algebras.Products.html#1139" class="Bound">𝓤</a><a id="1868" class="Symbol">)</a> <a id="1870" href="Algebras.Products.html#714" class="Bound">𝑆</a>

 <a id="1874" href="Algebras.Products.html#1825" class="Function">⨅&#39;</a> <a id="1877" href="Algebras.Products.html#1877" class="Bound">𝒜</a> <a id="1879" class="Symbol">=</a> <a id="1881" class="Keyword">record</a> <a id="1888" class="Symbol">{</a> <a id="1890" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1895" class="Symbol">=</a> <a id="1897" class="Symbol">∀</a> <a id="1899" href="Algebras.Products.html#1899" class="Bound">i</a> <a id="1901" class="Symbol">→</a> <a id="1903" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1908" class="Symbol">(</a><a id="1909" href="Algebras.Products.html#1877" class="Bound">𝒜</a> <a id="1911" href="Algebras.Products.html#1899" class="Bound">i</a><a id="1912" class="Symbol">)</a> <a id="1914" class="Symbol">;</a>                 <a id="1932" class="Comment">-- domain</a>
                 <a id="1959" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1962" class="Symbol">=</a> <a id="1964" class="Symbol">λ</a> <a id="1966" href="Algebras.Products.html#1966" class="Bound">𝑓</a> <a id="1968" href="Algebras.Products.html#1968" class="Bound">𝑎</a> <a id="1970" href="Algebras.Products.html#1970" class="Bound">i</a> <a id="1972" class="Symbol">→</a> <a id="1974" class="Symbol">(</a><a id="1975" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1978" class="Symbol">(</a><a id="1979" href="Algebras.Products.html#1877" class="Bound">𝒜</a> <a id="1981" href="Algebras.Products.html#1970" class="Bound">i</a><a id="1982" class="Symbol">))</a> <a id="1985" href="Algebras.Products.html#1966" class="Bound">𝑓</a> <a id="1987" class="Symbol">λ</a> <a id="1989" href="Algebras.Products.html#1989" class="Bound">x</a> <a id="1991" class="Symbol">→</a> <a id="1993" href="Algebras.Products.html#1968" class="Bound">𝑎</a> <a id="1995" href="Algebras.Products.html#1989" class="Bound">x</a> <a id="1997" href="Algebras.Products.html#1970" class="Bound">i</a> <a id="1999" class="Symbol">}</a> <a id="2001" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2276" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="2279" class="Symbol">:</a> <a id="2281" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2290" class="Symbol">→</a> <a id="2292" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2301" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="2304" href="Algebras.Products.html#2304" class="Bound">𝓤</a> <a id="2306" class="Symbol">=</a> <a id="2308" href="Algebras.Products.html#728" class="Bound">𝓞</a> <a id="2310" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2312" href="Algebras.Products.html#730" class="Bound">𝓥</a> <a id="2314" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2316" href="Algebras.Products.html#2304" class="Bound">𝓤</a> <a id="2318" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) \_`.<sup>[1](Algebras.Products.html#fn1)</sup>

Later we will formally state and prove that, given an arbitrary class `𝒦` of algebras, the product of all subalgebras of algebras in the class belongs to the class  `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise. In fact, it is not immediately clear (to this author, at least) how to even express the product of an entire class of algebras as a dependent type. However, with a sufficient amount of mindful meditation, the right type reveals itself.<sup>[2](Algebras.Products.html#fn2)</sup>

The solution is the \af{class-product} type whose construction is the main goal of this section. To begin, we need a type that will serve to index the class, as well as the product of its members.

<pre class="Agda">

<a id="3422" class="Keyword">module</a> <a id="class-products"></a><a id="3429" href="Algebras.Products.html#3429" class="Module">class-products</a> <a id="3444" class="Symbol">{</a><a id="3445" href="Algebras.Products.html#3445" class="Bound">𝓤</a> <a id="3447" class="Symbol">:</a> <a id="3449" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="3457" class="Symbol">}</a> <a id="3459" class="Symbol">(</a><a id="3460" href="Algebras.Products.html#3460" class="Bound">𝒦</a> <a id="3462" class="Symbol">:</a> <a id="3464" href="Relations.Discrete.html#1638" class="Function">Pred</a> <a id="3469" class="Symbol">(</a><a id="3470" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3478" href="Algebras.Products.html#3445" class="Bound">𝓤</a> <a id="3480" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="3481" class="Symbol">)(</a><a id="3483" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="3486" href="Algebras.Products.html#3445" class="Bound">𝓤</a><a id="3487" class="Symbol">))</a> <a id="3490" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="3498" href="Algebras.Products.html#3498" class="Function">ℑ</a> <a id="3500" class="Symbol">:</a> <a id="3502" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="3505" href="Algebras.Products.html#3445" class="Bound">𝓤</a> <a id="3507" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="3510" href="Algebras.Products.html#3498" class="Function">ℑ</a> <a id="3512" class="Symbol">=</a> <a id="3514" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="3516" href="Algebras.Products.html#3516" class="Bound">𝑨</a> <a id="3518" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="3520" class="Symbol">(</a><a id="3521" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3529" href="Algebras.Products.html#3445" class="Bound">𝓤</a> <a id="3531" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="3532" class="Symbol">)</a> <a id="3534" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="3536" class="Symbol">(</a><a id="3537" href="Algebras.Products.html#3516" class="Bound">𝑨</a> <a id="3539" href="Relations.Discrete.html#2494" class="Function Operator">∈</a> <a id="3541" href="Algebras.Products.html#3460" class="Bound">𝒦</a><a id="3542" class="Symbol">)</a>

</pre>

Taking the product over the index type ℑ requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="3889" href="Algebras.Products.html#3889" class="Function">𝔄</a> <a id="3891" class="Symbol">:</a> <a id="3893" href="Algebras.Products.html#3498" class="Function">ℑ</a> <a id="3895" class="Symbol">→</a> <a id="3897" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="3905" href="Algebras.Products.html#3445" class="Bound">𝓤</a> <a id="3907" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="3910" href="Algebras.Products.html#3889" class="Function">𝔄</a> <a id="3912" class="Symbol">=</a> <a id="3914" class="Symbol">λ</a> <a id="3916" class="Symbol">(</a><a id="3917" href="Algebras.Products.html#3917" class="Bound">i</a> <a id="3919" class="Symbol">:</a> <a id="3921" href="Algebras.Products.html#3498" class="Function">ℑ</a><a id="3922" class="Symbol">)</a> <a id="3924" class="Symbol">→</a> <a id="3926" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a> <a id="3928" href="Algebras.Products.html#3917" class="Bound">i</a> <a id="3930" href="Overture.Preliminaries.html#12413" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="4046" href="Algebras.Products.html#4046" class="Function">class-product</a> <a id="4060" class="Symbol">:</a> <a id="4062" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4070" class="Symbol">(</a><a id="4071" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="4074" href="Algebras.Products.html#3445" class="Bound">𝓤</a><a id="4075" class="Symbol">)</a> <a id="4077" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="4080" href="Algebras.Products.html#4046" class="Function">class-product</a> <a id="4094" class="Symbol">=</a> <a id="4096" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="4098" href="Algebras.Products.html#3889" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> The underscore is merely a placeholder for the universe of the predicate type and needn't concern us here.</span>

<sup>2</sup><span class="footnote" id="fn2"> Readers are encouraged to derive for themselves a type that represents the product of all algebras satisfying a given predicate. It is a good exercise. (*Hint*. The answer is not `Π 𝒦`. Although the latter is a valid type, it represnts not the product of algebras in `𝒦`, but rather the assertion that every algebra of type `Algebra 𝓤 𝑆` belongs to `𝒦`.)</span>

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

