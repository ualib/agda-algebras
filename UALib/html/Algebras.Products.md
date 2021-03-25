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

<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="Algebras.Signatures.html#1239" class="Function">Signature</a><a id="679" class="Symbol">;</a> <a id="681" href="Overture.Preliminaries.html#6850" class="Generalizable">𝓞</a><a id="682" class="Symbol">;</a> <a id="684" href="Universes.html#262" class="Generalizable">𝓥</a><a id="685" class="Symbol">)</a>

<a id="688" class="Keyword">module</a> <a id="695" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="713" class="Symbol">{</a><a id="714" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="716" class="Symbol">:</a> <a id="718" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="728" href="Overture.Preliminaries.html#6850" class="Generalizable">𝓞</a> <a id="730" href="Universes.html#262" class="Generalizable">𝓥</a><a id="731" class="Symbol">}</a> <a id="733" class="Keyword">where</a>

<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="770" class="Keyword">hiding</a> <a id="777" class="Symbol">(</a><a id="778" href="Overture.Preliminaries.html#6850" class="Generalizable">𝓞</a><a id="779" class="Symbol">;</a> <a id="781" href="Universes.html#262" class="Generalizable">𝓥</a><a id="782" class="Symbol">)</a> <a id="784" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a \defn{product of} \ab 𝑆-\defn{algebras} is represented by the following type.

<pre class="Agda">

<a id="1129" class="Keyword">module</a> <a id="1136" href="Algebras.Products.html#1136" class="Module">_</a> <a id="1138" class="Symbol">{</a><a id="1139" href="Algebras.Products.html#1139" class="Bound">𝓤</a> <a id="1141" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1143" class="Symbol">:</a> <a id="1145" href="Universes.html#205" class="Postulate">Universe</a><a id="1153" class="Symbol">}{</a><a id="1155" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1161" href="Universes.html#403" class="Function Operator">̇</a> <a id="1163" class="Symbol">}</a> <a id="1165" class="Keyword">where</a>

 <a id="1173" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="1175" class="Symbol">:</a> <a id="1177" class="Symbol">(</a><a id="1178" href="Algebras.Products.html#1178" class="Bound">𝒜</a> <a id="1180" class="Symbol">:</a> <a id="1182" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1184" class="Symbol">→</a> <a id="1186" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1194" href="Algebras.Products.html#1139" class="Bound">𝓤</a> <a id="1196" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="1198" class="Symbol">)</a> <a id="1200" class="Symbol">→</a> <a id="1202" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1210" class="Symbol">(</a><a id="1211" href="Algebras.Products.html#1141" class="Bound">𝓘</a> <a id="1213" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1215" href="Algebras.Products.html#1139" class="Bound">𝓤</a><a id="1216" class="Symbol">)</a> <a id="1218" href="Algebras.Products.html#714" class="Bound">𝑆</a>

 <a id="1222" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="1224" href="Algebras.Products.html#1224" class="Bound">𝒜</a> <a id="1226" class="Symbol">=</a> <a id="1228" class="Symbol">(</a><a id="1229" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1231" href="Algebras.Products.html#1231" class="Bound">i</a> <a id="1233" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1235" href="Algebras.Products.html#1155" class="Bound">I</a> <a id="1237" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1239" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a> <a id="1241" href="Algebras.Products.html#1224" class="Bound">𝒜</a> <a id="1243" href="Algebras.Products.html#1231" class="Bound">i</a> <a id="1245" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a><a id="1246" class="Symbol">)</a> <a id="1248" href="MGS-MLTT.html#2929" class="InductiveConstructor Operator">,</a>            <a id="1261" class="Comment">-- domain of the product algebra</a>
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

<a id="ov"></a><a id="2276" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="2279" class="Symbol">:</a> <a id="2281" href="Universes.html#205" class="Postulate">Universe</a> <a id="2290" class="Symbol">→</a> <a id="2292" href="Universes.html#205" class="Postulate">Universe</a>
<a id="2301" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="2304" href="Algebras.Products.html#2304" class="Bound">𝓤</a> <a id="2306" class="Symbol">=</a> <a id="2308" href="Algebras.Products.html#728" class="Bound">𝓞</a> <a id="2310" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2312" href="Algebras.Products.html#730" class="Bound">𝓥</a> <a id="2314" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2316" href="Algebras.Products.html#2304" class="Bound">𝓤</a> <a id="2318" href="Universes.html#181" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) 𝓦`, for some type `𝓦`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is definitely *not* what we want.  To see why, recall that `Pred (Algebra 𝓤 𝑆) 𝓦`, is just an alias for the function type \af{Algebra}~\ab 𝓤~\ab 𝑆~\as →~\ab 𝓦\af ̇. We interpret the latter semantically by taking \ab 𝒦~\ab 𝑨 to be the assertion that \ab 𝒦~\ab 𝑨 belongs to \ab 𝒦~\ab 𝑨, denoted \ab 𝑨 ∈ \ab 𝒦. Therefore, by definition, we have

`Π 𝒦 = Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝒦 𝑨`<br>
&nbsp; &nbsp; &nbsp; `= Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦`.

Semantically, this is the assertion that *every algebra of type* `Algebra 𝓤 𝑆` *belongs to* `𝒦`, and this bears little resemblance to the product of algebras that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra 𝓤 𝑆) → 𝓦 ̇`) and the type `Algebra 𝓤 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra 𝓤 𝑆` belonging to `𝒦`.<sup>[1](Algebras.Product.html#fn1)</sup>

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.<sup>[2](Algebras.Product.html#fn2)</sup>

<pre class="Agda">

<a id="4215" class="Keyword">module</a> <a id="class-products"></a><a id="4222" href="Algebras.Products.html#4222" class="Module">class-products</a> <a id="4237" class="Symbol">{</a><a id="4238" href="Algebras.Products.html#4238" class="Bound">𝓤</a> <a id="4240" class="Symbol">:</a> <a id="4242" href="Universes.html#205" class="Postulate">Universe</a><a id="4250" class="Symbol">}</a> <a id="4252" class="Symbol">(</a><a id="4253" href="Algebras.Products.html#4253" class="Bound">𝒦</a> <a id="4255" class="Symbol">:</a> <a id="4257" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="4262" class="Symbol">(</a><a id="4263" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4271" href="Algebras.Products.html#4238" class="Bound">𝓤</a> <a id="4273" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="4274" class="Symbol">)(</a><a id="4276" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="4279" href="Algebras.Products.html#4238" class="Bound">𝓤</a><a id="4280" class="Symbol">))</a> <a id="4283" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="4291" href="Algebras.Products.html#4291" class="Function">ℑ</a> <a id="4293" class="Symbol">:</a> <a id="4295" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="4298" href="Algebras.Products.html#4238" class="Bound">𝓤</a> <a id="4300" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4303" href="Algebras.Products.html#4291" class="Function">ℑ</a> <a id="4305" class="Symbol">=</a> <a id="4307" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4309" href="Algebras.Products.html#4309" class="Bound">𝑨</a> <a id="4311" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4313" class="Symbol">(</a><a id="4314" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4322" href="Algebras.Products.html#4238" class="Bound">𝓤</a> <a id="4324" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="4325" class="Symbol">)</a> <a id="4327" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4329" class="Symbol">(</a><a id="4330" href="Algebras.Products.html#4309" class="Bound">𝑨</a> <a id="4332" href="Relations.Discrete.html#2419" class="Function Operator">∈</a> <a id="4334" href="Algebras.Products.html#4253" class="Bound">𝒦</a><a id="4335" class="Symbol">)</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="4684" href="Algebras.Products.html#4684" class="Function">𝔄</a> <a id="4686" class="Symbol">:</a> <a id="4688" href="Algebras.Products.html#4291" class="Function">ℑ</a> <a id="4690" class="Symbol">→</a> <a id="4692" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4700" href="Algebras.Products.html#4238" class="Bound">𝓤</a> <a id="4702" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="4705" href="Algebras.Products.html#4684" class="Function">𝔄</a> <a id="4707" class="Symbol">=</a> <a id="4709" class="Symbol">λ</a> <a id="4711" class="Symbol">(</a><a id="4712" href="Algebras.Products.html#4712" class="Bound">i</a> <a id="4714" class="Symbol">:</a> <a id="4716" href="Algebras.Products.html#4291" class="Function">ℑ</a><a id="4717" class="Symbol">)</a> <a id="4719" class="Symbol">→</a> <a id="4721" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a> <a id="4723" href="Algebras.Products.html#4712" class="Bound">i</a> <a id="4725" href="Overture.Preliminaries.html#12400" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="4841" href="Algebras.Products.html#4841" class="Function">class-product</a> <a id="4855" class="Symbol">:</a> <a id="4857" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4865" class="Symbol">(</a><a id="4866" href="Algebras.Products.html#2276" class="Function">ov</a> <a id="4869" href="Algebras.Products.html#4238" class="Bound">𝓤</a><a id="4870" class="Symbol">)</a> <a id="4872" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="4875" href="Algebras.Products.html#4841" class="Function">class-product</a> <a id="4889" class="Symbol">=</a> <a id="4891" href="Algebras.Products.html#1173" class="Function">⨅</a> <a id="4893" href="Algebras.Products.html#4684" class="Function">𝔄</a>

</pre>

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.



-----------------------

<sup>1</sup><span class="footnote" id="fn1"> If you haven't already seen this before, give it some thought and see if the correct type comes to you organically.</span>

<sup>2</sup><span class="footnote" id="fn2"> **Unicode Hints**. Some of our types are denoted with with Gothic ("mathfrak") symbols. To produce them in [agda2-mode][], type `\Mf` followed by a letter. For example, `\MfI` ↝ `ℑ`.</span>

[← Algebras.Algebras](Algebras.Algebras.html)
<span style="float:right;">[Algebras.Congruences →](Algebras.Congruences.html)</span>

{% include UALib.Links.md %}

<!--

Alternatively, we could have defined the class product in a way that explicitly displays the index, like so.

 class-product' : Pred (Algebra 𝓤 𝑆)(ov 𝓤) → Algebra (𝓧 ⊔ ov 𝓤) 𝑆
 class-product' 𝒦 = ⨅ λ (i : (Σ 𝑨 ꞉ (Algebra 𝓤 𝑆) , (𝑨 ∈ 𝒦) × (X → ∣ 𝑨 ∣))) → ∣ i ∣

-->

