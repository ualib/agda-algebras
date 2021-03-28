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

<a id="631" class="Keyword">open</a> <a id="636" class="Keyword">import</a> <a id="643" href="Algebras.Signatures.html" class="Module">Algebras.Signatures</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="Algebras.Signatures.html#1239" class="Function">Signature</a><a id="679" class="Symbol">;</a> <a id="681" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="682" class="Symbol">;</a> <a id="684" href="Universes.html#262" class="Generalizable">𝓥</a><a id="685" class="Symbol">)</a>

<a id="688" class="Keyword">module</a> <a id="695" href="Algebras.Products.html" class="Module">Algebras.Products</a> <a id="713" class="Symbol">{</a><a id="714" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="716" class="Symbol">:</a> <a id="718" href="Algebras.Signatures.html#1239" class="Function">Signature</a> <a id="728" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a> <a id="730" href="Universes.html#262" class="Generalizable">𝓥</a><a id="731" class="Symbol">}</a> <a id="733" class="Keyword">where</a>

<a id="740" class="Keyword">open</a> <a id="745" class="Keyword">import</a> <a id="752" href="Algebras.Algebras.html" class="Module">Algebras.Algebras</a> <a id="770" class="Keyword">hiding</a> <a id="777" class="Symbol">(</a><a id="778" href="Overture.Preliminaries.html#8157" class="Generalizable">𝓞</a><a id="779" class="Symbol">;</a> <a id="781" href="Universes.html#262" class="Generalizable">𝓥</a><a id="782" class="Symbol">)</a> <a id="784" class="Keyword">public</a>

</pre>

We must import the `Signature` type from the [Algebras.Signatures][] module first, before the `module` line, so that we may use it to declare the signature `𝑆` as a parameter of the [Algebras.Products][] module.

In the [UALib][] a *product of* 𝑆-*algebras* is represented by the following type.

<pre class="Agda">

<a id="1115" class="Keyword">module</a> <a id="1122" href="Algebras.Products.html#1122" class="Module">_</a> <a id="1124" class="Symbol">{</a><a id="1125" href="Algebras.Products.html#1125" class="Bound">𝓤</a> <a id="1127" href="Algebras.Products.html#1127" class="Bound">𝓘</a> <a id="1129" class="Symbol">:</a> <a id="1131" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="1139" class="Symbol">}{</a><a id="1141" href="Algebras.Products.html#1141" class="Bound">I</a> <a id="1143" class="Symbol">:</a> <a id="1145" href="Algebras.Products.html#1127" class="Bound">𝓘</a> <a id="1147" href="Universes.html#403" class="Function Operator">̇</a> <a id="1149" class="Symbol">}</a> <a id="1151" class="Keyword">where</a>

 <a id="1159" href="Algebras.Products.html#1159" class="Function">⨅</a> <a id="1161" class="Symbol">:</a> <a id="1163" class="Symbol">(</a><a id="1164" href="Algebras.Products.html#1164" class="Bound">𝒜</a> <a id="1166" class="Symbol">:</a> <a id="1168" href="Algebras.Products.html#1141" class="Bound">I</a> <a id="1170" class="Symbol">→</a> <a id="1172" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1180" href="Algebras.Products.html#1125" class="Bound">𝓤</a> <a id="1182" href="Algebras.Products.html#714" class="Bound">𝑆</a> <a id="1184" class="Symbol">)</a> <a id="1186" class="Symbol">→</a> <a id="1188" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="1196" class="Symbol">(</a><a id="1197" href="Algebras.Products.html#1127" class="Bound">𝓘</a> <a id="1199" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1201" href="Algebras.Products.html#1125" class="Bound">𝓤</a><a id="1202" class="Symbol">)</a> <a id="1204" href="Algebras.Products.html#714" class="Bound">𝑆</a>

 <a id="1208" href="Algebras.Products.html#1159" class="Function">⨅</a> <a id="1210" href="Algebras.Products.html#1210" class="Bound">𝒜</a> <a id="1212" class="Symbol">=</a> <a id="1214" class="Symbol">(</a><a id="1215" href="MGS-MLTT.html#3635" class="Function">Π</a> <a id="1217" href="Algebras.Products.html#1217" class="Bound">i</a> <a id="1219" href="MGS-MLTT.html#3635" class="Function">꞉</a> <a id="1221" href="Algebras.Products.html#1141" class="Bound">I</a> <a id="1223" href="MGS-MLTT.html#3635" class="Function">,</a> <a id="1225" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="1227" href="Algebras.Products.html#1210" class="Bound">𝒜</a> <a id="1229" href="Algebras.Products.html#1217" class="Bound">i</a> <a id="1231" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a><a id="1232" class="Symbol">)</a> <a id="1234" href="Overture.Preliminaries.html#13063" class="InductiveConstructor Operator">,</a>            <a id="1247" class="Comment">-- domain of the product algebra</a>
       <a id="1287" class="Symbol">λ</a> <a id="1289" href="Algebras.Products.html#1289" class="Bound">𝑓</a> <a id="1291" href="Algebras.Products.html#1291" class="Bound">𝑎</a> <a id="1293" href="Algebras.Products.html#1293" class="Bound">i</a> <a id="1295" class="Symbol">→</a> <a id="1297" class="Symbol">(</a><a id="1298" href="Algebras.Products.html#1289" class="Bound">𝑓</a> <a id="1300" href="Algebras.Algebras.html#2989" class="Function Operator">̂</a> <a id="1302" href="Algebras.Products.html#1210" class="Bound">𝒜</a> <a id="1304" href="Algebras.Products.html#1293" class="Bound">i</a><a id="1305" class="Symbol">)</a> <a id="1307" class="Symbol">λ</a> <a id="1309" href="Algebras.Products.html#1309" class="Bound">x</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="Algebras.Products.html#1291" class="Bound">𝑎</a> <a id="1315" href="Algebras.Products.html#1309" class="Bound">x</a> <a id="1317" href="Algebras.Products.html#1293" class="Bound">i</a>   <a id="1321" class="Comment">-- basic operations of the product algebra</a>

</pre>

(Alternative acceptable notation for the domain of the product is `∀ i → ∣ 𝒜 i ∣`.)

The type just defined is the one that will be used throughout the [UALib][] whenever the product of an indexed collection of algebras (of type `Algebra`) is required.  However, for the sake of completeness, here is how one could define a type representing the product of algebras inhabiting the record type `algebra`.

<pre class="Agda">

 <a id="1796" class="Keyword">open</a> <a id="1801" href="Algebras.Algebras.html#1865" class="Module">algebra</a>

 <a id="1811" href="Algebras.Products.html#1811" class="Function">⨅&#39;</a> <a id="1814" class="Symbol">:</a> <a id="1816" class="Symbol">(</a><a id="1817" href="Algebras.Products.html#1817" class="Bound">𝒜</a> <a id="1819" class="Symbol">:</a> <a id="1821" href="Algebras.Products.html#1141" class="Bound">I</a> <a id="1823" class="Symbol">→</a> <a id="1825" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1833" href="Algebras.Products.html#1125" class="Bound">𝓤</a> <a id="1835" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="1836" class="Symbol">)</a> <a id="1838" class="Symbol">→</a> <a id="1840" href="Algebras.Algebras.html#1865" class="Record">algebra</a> <a id="1848" class="Symbol">(</a><a id="1849" href="Algebras.Products.html#1127" class="Bound">𝓘</a> <a id="1851" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="1853" href="Algebras.Products.html#1125" class="Bound">𝓤</a><a id="1854" class="Symbol">)</a> <a id="1856" href="Algebras.Products.html#714" class="Bound">𝑆</a>

 <a id="1860" href="Algebras.Products.html#1811" class="Function">⨅&#39;</a> <a id="1863" href="Algebras.Products.html#1863" class="Bound">𝒜</a> <a id="1865" class="Symbol">=</a> <a id="1867" class="Keyword">record</a> <a id="1874" class="Symbol">{</a> <a id="1876" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1881" class="Symbol">=</a> <a id="1883" class="Symbol">∀</a> <a id="1885" href="Algebras.Products.html#1885" class="Bound">i</a> <a id="1887" class="Symbol">→</a> <a id="1889" href="Algebras.Algebras.html#1960" class="Field">univ</a> <a id="1894" class="Symbol">(</a><a id="1895" href="Algebras.Products.html#1863" class="Bound">𝒜</a> <a id="1897" href="Algebras.Products.html#1885" class="Bound">i</a><a id="1898" class="Symbol">)</a> <a id="1900" class="Symbol">;</a>                 <a id="1918" class="Comment">-- domain</a>
                 <a id="1945" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1948" class="Symbol">=</a> <a id="1950" class="Symbol">λ</a> <a id="1952" href="Algebras.Products.html#1952" class="Bound">𝑓</a> <a id="1954" href="Algebras.Products.html#1954" class="Bound">𝑎</a> <a id="1956" href="Algebras.Products.html#1956" class="Bound">i</a> <a id="1958" class="Symbol">→</a> <a id="1960" class="Symbol">(</a><a id="1961" href="Algebras.Algebras.html#1973" class="Field">op</a> <a id="1964" class="Symbol">(</a><a id="1965" href="Algebras.Products.html#1863" class="Bound">𝒜</a> <a id="1967" href="Algebras.Products.html#1956" class="Bound">i</a><a id="1968" class="Symbol">))</a> <a id="1971" href="Algebras.Products.html#1952" class="Bound">𝑓</a> <a id="1973" class="Symbol">λ</a> <a id="1975" href="Algebras.Products.html#1975" class="Bound">x</a> <a id="1977" class="Symbol">→</a> <a id="1979" href="Algebras.Products.html#1954" class="Bound">𝑎</a> <a id="1981" href="Algebras.Products.html#1975" class="Bound">x</a> <a id="1983" href="Algebras.Products.html#1956" class="Bound">i</a> <a id="1985" class="Symbol">}</a> <a id="1987" class="Comment">-- basic operations</a>

</pre>



**Notation**. Given a signature `𝑆 : Signature 𝓞 𝓥`, the type `Algebra 𝓤 𝑆` has universe `𝓞 ⊔ 𝓥 ⊔ 𝓤 ⁺`.  Such types occur so often in the [UALib][] that it is worthwhile to define the following shorthand for their universes.

<pre class="Agda">

<a id="ov"></a><a id="2262" href="Algebras.Products.html#2262" class="Function">ov</a> <a id="2265" class="Symbol">:</a> <a id="2267" href="Agda.Primitive.html#423" class="Postulate">Universe</a> <a id="2276" class="Symbol">→</a> <a id="2278" href="Agda.Primitive.html#423" class="Postulate">Universe</a>
<a id="2287" href="Algebras.Products.html#2262" class="Function">ov</a> <a id="2290" href="Algebras.Products.html#2290" class="Bound">𝓤</a> <a id="2292" class="Symbol">=</a> <a id="2294" href="Algebras.Products.html#728" class="Bound">𝓞</a> <a id="2296" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2298" href="Algebras.Products.html#730" class="Bound">𝓥</a> <a id="2300" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="2302" href="Algebras.Products.html#2290" class="Bound">𝓤</a> <a id="2304" href="Agda.Primitive.html#606" class="Primitive Operator">⁺</a>

</pre>



#### <a id="products-of-classes-of-algebras">Products of classes of algebras</a>

An arbitrary class `𝒦` of algebras is represented as a predicate over the type `Algebra 𝓤 𝑆`, for some universe level `𝓤` and signature `𝑆`. That is, `𝒦 : Pred (Algebra 𝓤 𝑆) 𝓦`, for some type `𝓦`. Later we will formally state and prove that the product of all subalgebras of algebras in `𝒦` belongs to the class `SP(𝒦)` of subalgebras of products of algebras in `𝒦`. That is, `⨅ S(𝒦) ∈ SP(𝒦 )`. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary (nonindexed) families such as `𝒦` or `S(𝒦)`. Observe that `Π 𝒦` is definitely *not* what we want.  To see why, recall that `Pred (Algebra 𝓤 𝑆) 𝓦`, is just an alias for the function type `Algebra 𝓤 𝑆 → 𝓦 ̇`. We interpret the latter semantically by taking `𝒦 𝑨` (and `𝑨 ∈ 𝒦`) to denote the assertion that `𝒦 𝑨` belongs to `𝒦`. Therefore, by definition, we have

`Π 𝒦 = Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝒦 𝑨`<br>
&nbsp; &nbsp; &nbsp; `= Π 𝑨 ꞉ (Algebra 𝓤 𝑆) , 𝑨 ∈ 𝒦`.

Semantically, this is the assertion that *every algebra of type* `Algebra 𝓤 𝑆` *belongs to* `𝒦`, and this bears little resemblance to the product of algebras that we seek.

What we need is a type that serves to index the class `𝒦`, and a function `𝔄` that maps an index to the inhabitant of `𝒦` at that index. But `𝒦` is a predicate (of type `(Algebra 𝓤 𝑆) → 𝓦 ̇`) and the type `Algebra 𝓤 𝑆` seems rather nebulous in that there is no natural indexing class with which to "enumerate" all inhabitants of `Algebra 𝓤 𝑆` belonging to `𝒦`.<sup>[1](Algebras.Product.html#fn1)</sup>

The solution is to essentially take `𝒦` itself to be the indexing type, at least heuristically that is how one can view the type `ℑ` that we now define.<sup>[2](Algebras.Product.html#fn2)</sup>

<pre class="Agda">

<a id="4154" class="Keyword">module</a> <a id="class-products"></a><a id="4161" href="Algebras.Products.html#4161" class="Module">class-products</a> <a id="4176" class="Symbol">{</a><a id="4177" href="Algebras.Products.html#4177" class="Bound">𝓤</a> <a id="4179" class="Symbol">:</a> <a id="4181" href="Agda.Primitive.html#423" class="Postulate">Universe</a><a id="4189" class="Symbol">}</a> <a id="4191" class="Symbol">(</a><a id="4192" href="Algebras.Products.html#4192" class="Bound">𝒦</a> <a id="4194" class="Symbol">:</a> <a id="4196" href="Relations.Discrete.html#1534" class="Function">Pred</a> <a id="4201" class="Symbol">(</a><a id="4202" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4210" href="Algebras.Products.html#4177" class="Bound">𝓤</a> <a id="4212" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="4213" class="Symbol">)(</a><a id="4215" href="Algebras.Products.html#2262" class="Function">ov</a> <a id="4218" href="Algebras.Products.html#4177" class="Bound">𝓤</a><a id="4219" class="Symbol">))</a> <a id="4222" class="Keyword">where</a>

 <a id="class-products.ℑ"></a><a id="4230" href="Algebras.Products.html#4230" class="Function">ℑ</a> <a id="4232" class="Symbol">:</a> <a id="4234" href="Algebras.Products.html#2262" class="Function">ov</a> <a id="4237" href="Algebras.Products.html#4177" class="Bound">𝓤</a> <a id="4239" href="Universes.html#403" class="Function Operator">̇</a>
 <a id="4242" href="Algebras.Products.html#4230" class="Function">ℑ</a> <a id="4244" class="Symbol">=</a> <a id="4246" href="MGS-MLTT.html#3074" class="Function">Σ</a> <a id="4248" href="Algebras.Products.html#4248" class="Bound">𝑨</a> <a id="4250" href="MGS-MLTT.html#3074" class="Function">꞉</a> <a id="4252" class="Symbol">(</a><a id="4253" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4261" href="Algebras.Products.html#4177" class="Bound">𝓤</a> <a id="4263" href="Algebras.Products.html#714" class="Bound">𝑆</a><a id="4264" class="Symbol">)</a> <a id="4266" href="MGS-MLTT.html#3074" class="Function">,</a> <a id="4268" class="Symbol">(</a><a id="4269" href="Algebras.Products.html#4248" class="Bound">𝑨</a> <a id="4271" href="Relations.Discrete.html#2402" class="Function Operator">∈</a> <a id="4273" href="Algebras.Products.html#4192" class="Bound">𝒦</a><a id="4274" class="Symbol">)</a>

</pre>

Taking the product over the index type `ℑ` requires a function that maps an index `i : ℑ` to the corresponding algebra.  Each `i : ℑ` is a pair, `(𝑨 , p)`, where `𝑨` is an algebra and `p` is a proof that `𝑨` belongs to `𝒦`, so the function mapping an index to the corresponding algebra is simply the first projection.

<pre class="Agda">

 <a id="class-products.𝔄"></a><a id="4623" href="Algebras.Products.html#4623" class="Function">𝔄</a> <a id="4625" class="Symbol">:</a> <a id="4627" href="Algebras.Products.html#4230" class="Function">ℑ</a> <a id="4629" class="Symbol">→</a> <a id="4631" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4639" href="Algebras.Products.html#4177" class="Bound">𝓤</a> <a id="4641" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="4644" href="Algebras.Products.html#4623" class="Function">𝔄</a> <a id="4646" class="Symbol">=</a> <a id="4648" class="Symbol">λ</a> <a id="4650" class="Symbol">(</a><a id="4651" href="Algebras.Products.html#4651" class="Bound">i</a> <a id="4653" class="Symbol">:</a> <a id="4655" href="Algebras.Products.html#4230" class="Function">ℑ</a><a id="4656" class="Symbol">)</a> <a id="4658" class="Symbol">→</a> <a id="4660" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a> <a id="4662" href="Algebras.Products.html#4651" class="Bound">i</a> <a id="4664" href="Overture.Preliminaries.html#13759" class="Function Operator">∣</a>

</pre>

Finally, we define `class-product` which represents the product of all members of 𝒦.

<pre class="Agda">

 <a id="class-products.class-product"></a><a id="4780" href="Algebras.Products.html#4780" class="Function">class-product</a> <a id="4794" class="Symbol">:</a> <a id="4796" href="Algebras.Algebras.html#674" class="Function">Algebra</a> <a id="4804" class="Symbol">(</a><a id="4805" href="Algebras.Products.html#2262" class="Function">ov</a> <a id="4808" href="Algebras.Products.html#4177" class="Bound">𝓤</a><a id="4809" class="Symbol">)</a> <a id="4811" href="Algebras.Products.html#714" class="Bound">𝑆</a>
 <a id="4814" href="Algebras.Products.html#4780" class="Function">class-product</a> <a id="4828" class="Symbol">=</a> <a id="4830" href="Algebras.Products.html#1159" class="Function">⨅</a> <a id="4832" href="Algebras.Products.html#4623" class="Function">𝔄</a>

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

