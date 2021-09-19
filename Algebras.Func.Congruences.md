---
layout: default
title : "Algebras.Func.Congruences module (The Agda Universal Algebra Library)"
date : "2021-09-15"
author: "agda-algebras development team"
---

#### <a id="congruences-of-setoidalgebras">Congruences of Setoid Algebras</a>

This is the [Algebras.Func.Congruences][] module of the [Agda Universal Algebra Library][].

<pre class="Agda">

<a id="353" class="Symbol">{-#</a> <a id="357" class="Keyword">OPTIONS</a> <a id="365" class="Pragma">--without-K</a> <a id="377" class="Pragma">--exact-split</a> <a id="391" class="Pragma">--safe</a> <a id="398" class="Symbol">#-}</a>

<a id="403" class="Keyword">open</a> <a id="408" class="Keyword">import</a> <a id="415" href="Algebras.Basic.html" class="Module">Algebras.Basic</a> <a id="430" class="Keyword">using</a> <a id="436" class="Symbol">(</a><a id="437" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="439" class="Symbol">;</a> <a id="441" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a> <a id="443" class="Symbol">;</a> <a id="445" href="Algebras.Basic.html#3858" class="Function">Signature</a><a id="454" class="Symbol">)</a>

<a id="457" class="Keyword">module</a> <a id="464" href="Algebras.Func.Congruences.html" class="Module">Algebras.Func.Congruences</a> <a id="490" class="Symbol">{</a><a id="491" href="Algebras.Func.Congruences.html#491" class="Bound">𝑆</a> <a id="493" class="Symbol">:</a> <a id="495" href="Algebras.Basic.html#3858" class="Function">Signature</a> <a id="505" href="Algebras.Basic.html#1130" class="Generalizable">𝓞</a> <a id="507" href="Algebras.Basic.html#1132" class="Generalizable">𝓥</a><a id="508" class="Symbol">}</a> <a id="510" class="Keyword">where</a>

<a id="517" class="Comment">-- Imports from the Agda Standard Library ---------------------------------------</a>
<a id="599" class="Keyword">open</a> <a id="604" class="Keyword">import</a> <a id="611" href="Function.html" class="Module">Function</a>              <a id="633" class="Keyword">using</a> <a id="639" class="Symbol">(</a> <a id="641" href="Function.Base.html#615" class="Function">id</a> <a id="644" class="Symbol">)</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="Function.Bundles.html" class="Module">Function.Bundles</a>      <a id="680" class="Keyword">using</a> <a id="686" class="Symbol">(</a> <a id="688" href="Function.Bundles.html#1868" class="Record">Func</a> <a id="693" class="Symbol">)</a>
<a id="695" class="Keyword">open</a> <a id="700" class="Keyword">import</a> <a id="707" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>        <a id="729" class="Keyword">using</a> <a id="735" class="Symbol">(</a> <a id="737" href="Agda.Primitive.html#810" class="Primitive Operator">_⊔_</a> <a id="741" class="Symbol">;</a> <a id="743" href="Agda.Primitive.html#597" class="Postulate">Level</a> <a id="749" class="Symbol">)</a> <a id="751" class="Keyword">renaming</a> <a id="760" class="Symbol">(</a> <a id="762" href="Agda.Primitive.html#326" class="Primitive">Set</a> <a id="766" class="Symbol">to</a> <a id="769" class="Primitive">Type</a> <a id="774" class="Symbol">)</a>
<a id="776" class="Keyword">open</a> <a id="781" class="Keyword">import</a> <a id="788" href="Data.Product.html" class="Module">Data.Product</a>          <a id="810" class="Keyword">using</a> <a id="816" class="Symbol">(</a> <a id="818" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a> <a id="822" class="Symbol">;</a> <a id="824" href="Data.Product.html#916" class="Function">Σ-syntax</a> <a id="833" class="Symbol">)</a>
<a id="835" class="Keyword">open</a> <a id="840" class="Keyword">import</a> <a id="847" href="Relation.Binary.html" class="Module">Relation.Binary</a>       <a id="869" class="Keyword">using</a> <a id="875" class="Symbol">(</a> <a id="877" href="Relation.Binary.Bundles.html#1009" class="Record">Setoid</a> <a id="884" class="Symbol">;</a> <a id="886" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="900" class="Symbol">)</a> <a id="902" class="Keyword">renaming</a> <a id="911" class="Symbol">(</a> <a id="913" href="Relation.Binary.Core.html#882" class="Function">Rel</a> <a id="917" class="Symbol">to</a> <a id="920" class="Function">BinRel</a> <a id="927" class="Symbol">)</a>
<a id="929" class="Keyword">open</a> <a id="934" class="Keyword">import</a> <a id="941" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a>
                                  <a id="1013" class="Keyword">using</a> <a id="1019" class="Symbol">(</a> <a id="1021" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="1026" class="Symbol">)</a>

<a id="1029" class="Comment">-- Imports from the Agda Universal Algebras Library ------------------------------</a>
<a id="1112" class="Keyword">open</a> <a id="1117" class="Keyword">import</a> <a id="1124" href="Overture.Preliminaries.html" class="Module">Overture.Preliminaries</a>     <a id="1151" class="Keyword">using</a> <a id="1157" class="Symbol">(</a> <a id="1159" href="Overture.Preliminaries.html#4383" class="Function Operator">∣_∣</a>  <a id="1164" class="Symbol">;</a> <a id="1166" href="Overture.Preliminaries.html#4421" class="Function Operator">∥_∥</a>  <a id="1171" class="Symbol">)</a>
<a id="1173" class="Keyword">open</a> <a id="1178" class="Keyword">import</a> <a id="1185" href="Relations.Discrete.html" class="Module">Relations.Discrete</a>         <a id="1212" class="Keyword">using</a> <a id="1218" class="Symbol">(</a> <a id="1220" href="Relations.Discrete.html#4655" class="Function Operator">0[_]</a> <a id="1225" class="Symbol">;</a> <a id="1227" href="Relations.Discrete.html#7001" class="Function Operator">_|:_</a> <a id="1232" class="Symbol">)</a>
<a id="1234" class="Keyword">open</a> <a id="1239" class="Keyword">import</a> <a id="1246" href="Algebras.Func.Basic.html" class="Module">Algebras.Func.Basic</a> <a id="1266" class="Symbol">{</a><a id="1267" class="Argument">𝑆</a> <a id="1269" class="Symbol">=</a> <a id="1271" href="Algebras.Func.Congruences.html#491" class="Bound">𝑆</a><a id="1272" class="Symbol">}</a> <a id="1274" class="Keyword">using</a> <a id="1280" class="Symbol">(</a> <a id="1282" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="1285" class="Symbol">;</a> <a id="1287" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1301" class="Symbol">;</a> <a id="1303" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[_]</a> <a id="1308" class="Symbol">;</a> <a id="1310" href="Algebras.Func.Basic.html#4078" class="Function Operator">_̂_</a> <a id="1314" class="Symbol">)</a>
<a id="1316" class="Keyword">open</a> <a id="1321" class="Keyword">import</a> <a id="1328" href="Relations.Quotients.html" class="Module">Relations.Quotients</a>        <a id="1355" class="Keyword">using</a>  <a id="1362" class="Symbol">(</a> <a id="1364" href="Relations.Quotients.html#1806" class="Function">Equivalence</a> <a id="1376" class="Symbol">)</a>
<a id="1378" class="Keyword">open</a> <a id="1383" class="Keyword">import</a> <a id="1390" href="Relations.Func.Quotients.html" class="Module">Relations.Func.Quotients</a>   <a id="1417" class="Keyword">using</a> <a id="1423" class="Symbol">(</a> <a id="1425" href="Relations.Func.Quotients.html#2708" class="Function Operator">⟪_⟫</a> <a id="1429" class="Symbol">;</a> <a id="1431" href="Relations.Func.Quotients.html#2450" class="Function Operator">_/_</a> <a id="1435" class="Symbol">;</a> <a id="1437" href="Relations.Func.Quotients.html#2991" class="Function Operator">⟪_∼_⟫-elim</a> <a id="1448" class="Symbol">)</a>

<a id="1451" class="Keyword">private</a> <a id="1459" class="Keyword">variable</a> <a id="1468" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="1470" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a> <a id="1472" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a> <a id="1474" class="Symbol">:</a> <a id="1476" href="Agda.Primitive.html#597" class="Postulate">Level</a>

</pre>

We now define the function `compatible` so that, if `𝑨` denotes an algebra and `R` a binary relation, then `compatible 𝑨 R` will represent the assertion that `R` is *compatible* with all basic operations of `𝑨`. The formal definition is immediate since all the work is done by the relation `|:`, which we defined above (see [Relations.Discrete][]).

<pre class="Agda">

<a id="1859" class="Comment">-- SetoidAlgebra compatibility with binary relation</a>
<a id="_∣≈_"></a><a id="1911" href="Algebras.Func.Congruences.html#1911" class="Function Operator">_∣≈_</a> <a id="1916" class="Symbol">:</a> <a id="1918" class="Symbol">(</a><a id="1919" href="Algebras.Func.Congruences.html#1919" class="Bound">𝑨</a> <a id="1921" class="Symbol">:</a> <a id="1923" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="1937" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="1939" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="1940" class="Symbol">)</a> <a id="1942" class="Symbol">→</a> <a id="1944" href="Algebras.Func.Congruences.html#920" class="Function">BinRel</a> <a id="1951" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="1954" href="Algebras.Func.Congruences.html#1919" class="Bound">𝑨</a> <a id="1956" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="1958" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a> <a id="1960" class="Symbol">→</a> <a id="1962" href="Algebras.Func.Congruences.html#769" class="Primitive">Type</a> <a id="1967" class="Symbol">_</a>
<a id="1969" href="Algebras.Func.Congruences.html#1969" class="Bound">𝑨</a> <a id="1971" href="Algebras.Func.Congruences.html#1911" class="Function Operator">∣≈</a> <a id="1974" href="Algebras.Func.Congruences.html#1974" class="Bound">R</a> <a id="1976" class="Symbol">=</a> <a id="1978" class="Symbol">∀</a> <a id="1980" href="Algebras.Func.Congruences.html#1980" class="Bound">𝑓</a> <a id="1982" class="Symbol">→</a> <a id="1984" class="Symbol">(</a><a id="1985" href="Algebras.Func.Congruences.html#1980" class="Bound">𝑓</a> <a id="1987" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="1989" href="Algebras.Func.Congruences.html#1969" class="Bound">𝑨</a><a id="1990" class="Symbol">)</a> <a id="1992" href="Relations.Discrete.html#7001" class="Function Operator">|:</a> <a id="1995" href="Algebras.Func.Congruences.html#1974" class="Bound">R</a>

</pre>

A *congruence relation* of an algebra `𝑨` is defined to be an equivalence relation that is compatible with the basic operations of `𝑨`.  This concept can be represented in a number of alternative but equivalent ways.
Formally, we define a record type (`IsCongruence`) to represent the property of being a congruence, and we define a Sigma type (`Con`) to represent the type of congruences of a given algebra.

Congruences should obviously contain the equality relation on the underlying setoid. That is, they must be reflexive. Unfortunately this doesn't come for free (e.g., as part of the definition of `IsEquivalence` on Setoid), so we must add the field `reflexive` to the definition of `IsCongruence`. (In fact, we should probably redefine equivalence relation on setiods to be reflexive with respect to the underying setoid equality (and not just with respect to _≡_).)

<pre class="Agda">

<a id="2901" class="Keyword">module</a> <a id="2908" href="Algebras.Func.Congruences.html#2908" class="Module">_</a> <a id="2910" class="Symbol">(</a><a id="2911" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a> <a id="2913" class="Symbol">:</a> <a id="2915" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="2929" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="2931" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="2932" class="Symbol">)</a> <a id="2934" class="Keyword">where</a>

 <a id="2942" class="Keyword">open</a> <a id="2947" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a> <a id="2961" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a>  <a id="2964" class="Keyword">using</a> <a id="2970" class="Symbol">()</a>  <a id="2974" class="Keyword">renaming</a> <a id="2983" class="Symbol">(</a><a id="2984" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="2991" class="Symbol">to</a> <a id="2994" class="Field">A</a> <a id="2996" class="Symbol">)</a>
 <a id="2999" class="Keyword">open</a> <a id="3004" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a> <a id="3011" href="Algebras.Func.Congruences.html#2994" class="Field">A</a> <a id="3013" class="Keyword">using</a> <a id="3019" class="Symbol">(</a> <a id="3021" href="Relation.Binary.Bundles.html#1098" class="Field Operator">_≈_</a> <a id="3025" class="Symbol">)</a>

 <a id="3029" class="Keyword">record</a> <a id="3036" href="Algebras.Func.Congruences.html#3036" class="Record">IsCongruence</a> <a id="3049" class="Symbol">(</a><a id="3050" href="Algebras.Func.Congruences.html#3050" class="Bound">θ</a> <a id="3052" class="Symbol">:</a> <a id="3054" href="Algebras.Func.Congruences.html#920" class="Function">BinRel</a> <a id="3061" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="3064" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a> <a id="3066" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="3068" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="3069" class="Symbol">)</a> <a id="3071" class="Symbol">:</a> <a id="3073" href="Algebras.Func.Congruences.html#769" class="Primitive">Type</a> <a id="3078" class="Symbol">(</a><a id="3079" href="Algebras.Func.Congruences.html#505" class="Bound">𝓞</a> <a id="3081" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3083" href="Algebras.Func.Congruences.html#507" class="Bound">𝓥</a> <a id="3085" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3087" href="Algebras.Func.Congruences.html#2931" class="Bound">ρ</a> <a id="3089" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3091" href="Algebras.Func.Congruences.html#3068" class="Bound">ℓ</a> <a id="3093" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3095" href="Algebras.Func.Congruences.html#2929" class="Bound">α</a><a id="3096" class="Symbol">)</a>  <a id="3099" class="Keyword">where</a>
  <a id="3107" class="Keyword">constructor</a> <a id="3119" href="Algebras.Func.Congruences.html#3119" class="InductiveConstructor">mkcon</a>
  <a id="3127" class="Keyword">field</a>       <a id="3139" href="Algebras.Func.Congruences.html#3139" class="Field">reflexive</a> <a id="3149" class="Symbol">:</a> <a id="3151" class="Symbol">∀</a> <a id="3153" class="Symbol">{</a><a id="3154" href="Algebras.Func.Congruences.html#3154" class="Bound">a₀</a> <a id="3157" href="Algebras.Func.Congruences.html#3157" class="Bound">a₁</a><a id="3159" class="Symbol">}</a> <a id="3161" class="Symbol">→</a> <a id="3163" href="Algebras.Func.Congruences.html#3154" class="Bound">a₀</a> <a id="3166" href="Relation.Binary.Bundles.html#1098" class="Function Operator">≈</a> <a id="3168" href="Algebras.Func.Congruences.html#3157" class="Bound">a₁</a> <a id="3171" class="Symbol">→</a> <a id="3173" href="Algebras.Func.Congruences.html#3050" class="Bound">θ</a> <a id="3175" href="Algebras.Func.Congruences.html#3154" class="Bound">a₀</a> <a id="3178" href="Algebras.Func.Congruences.html#3157" class="Bound">a₁</a>
              <a id="3195" href="Algebras.Func.Congruences.html#3195" class="Field">is-equivalence</a> <a id="3210" class="Symbol">:</a> <a id="3212" href="Relation.Binary.Structures.html#1522" class="Record">IsEquivalence</a> <a id="3226" href="Algebras.Func.Congruences.html#3050" class="Bound">θ</a>
              <a id="3242" href="Algebras.Func.Congruences.html#3242" class="Field">is-compatible</a>  <a id="3257" class="Symbol">:</a> <a id="3259" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a> <a id="3261" href="Algebras.Func.Congruences.html#1911" class="Function Operator">∣≈</a> <a id="3264" href="Algebras.Func.Congruences.html#3050" class="Bound">θ</a>

  <a id="3269" href="Algebras.Func.Congruences.html#3269" class="Function">Eqv</a> <a id="3273" class="Symbol">:</a> <a id="3275" href="Relations.Quotients.html#1806" class="Function">Equivalence</a> <a id="3287" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="3290" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a> <a id="3292" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="3294" class="Symbol">{</a><a id="3295" href="Algebras.Func.Congruences.html#3068" class="Bound">ℓ</a><a id="3296" class="Symbol">}</a>
  <a id="3300" href="Algebras.Func.Congruences.html#3269" class="Function">Eqv</a> <a id="3304" class="Symbol">=</a> <a id="3306" href="Algebras.Func.Congruences.html#3050" class="Bound">θ</a> <a id="3308" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3310" href="Algebras.Func.Congruences.html#3195" class="Field">is-equivalence</a>

 <a id="3327" class="Keyword">open</a> <a id="3332" href="Algebras.Func.Congruences.html#3036" class="Module">IsCongruence</a> <a id="3345" class="Keyword">public</a>

 <a id="3354" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="3358" class="Symbol">:</a> <a id="3360" class="Symbol">{</a><a id="3361" href="Algebras.Func.Congruences.html#3361" class="Bound">ℓ</a> <a id="3363" class="Symbol">:</a> <a id="3365" href="Agda.Primitive.html#597" class="Postulate">Level</a><a id="3370" class="Symbol">}</a> <a id="3372" class="Symbol">→</a> <a id="3374" href="Algebras.Func.Congruences.html#769" class="Primitive">Type</a> <a id="3379" class="Symbol">(</a><a id="3380" href="Algebras.Func.Congruences.html#2929" class="Bound">α</a> <a id="3382" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3384" href="Algebras.Func.Congruences.html#2931" class="Bound">ρ</a> <a id="3386" href="Agda.Primitive.html#810" class="Primitive Operator">⊔</a> <a id="3388" href="Algebras.Func.Basic.html#1172" class="Function">ov</a> <a id="3391" href="Algebras.Func.Congruences.html#3361" class="Bound">ℓ</a><a id="3392" class="Symbol">)</a>
 <a id="3395" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="3399" class="Symbol">{</a><a id="3400" href="Algebras.Func.Congruences.html#3400" class="Bound">ℓ</a><a id="3401" class="Symbol">}</a> <a id="3403" class="Symbol">=</a> <a id="3405" href="Data.Product.html#916" class="Function">Σ[</a> <a id="3408" href="Algebras.Func.Congruences.html#3408" class="Bound">θ</a> <a id="3410" href="Data.Product.html#916" class="Function">∈</a> <a id="3412" class="Symbol">(</a> <a id="3414" href="Algebras.Func.Congruences.html#920" class="Function">BinRel</a> <a id="3421" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="3424" href="Algebras.Func.Congruences.html#2911" class="Bound">𝑨</a> <a id="3426" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="3428" href="Algebras.Func.Congruences.html#3400" class="Bound">ℓ</a> <a id="3430" class="Symbol">)</a> <a id="3432" href="Data.Product.html#916" class="Function">]</a> <a id="3434" href="Algebras.Func.Congruences.html#3036" class="Record">IsCongruence</a> <a id="3447" href="Algebras.Func.Congruences.html#3408" class="Bound">θ</a>

</pre>

Each of these types captures what it means to be a congruence and they are equivalent in the sense that each implies the other. One implication is the "uncurry" operation and the other is the second projection.

<pre class="Agda">

<a id="IsCongruence→Con"></a><a id="3688" href="Algebras.Func.Congruences.html#3688" class="Function">IsCongruence→Con</a> <a id="3705" class="Symbol">:</a> <a id="3707" class="Symbol">{</a><a id="3708" href="Algebras.Func.Congruences.html#3708" class="Bound">𝑨</a> <a id="3710" class="Symbol">:</a> <a id="3712" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="3726" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="3728" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="3729" class="Symbol">}(</a><a id="3731" href="Algebras.Func.Congruences.html#3731" class="Bound">θ</a> <a id="3733" class="Symbol">:</a> <a id="3735" href="Algebras.Func.Congruences.html#920" class="Function">BinRel</a> <a id="3742" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="3745" href="Algebras.Func.Congruences.html#3708" class="Bound">𝑨</a> <a id="3747" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="3749" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="3750" class="Symbol">)</a> <a id="3752" class="Symbol">→</a> <a id="3754" href="Algebras.Func.Congruences.html#3036" class="Record">IsCongruence</a> <a id="3767" href="Algebras.Func.Congruences.html#3708" class="Bound">𝑨</a> <a id="3769" href="Algebras.Func.Congruences.html#3731" class="Bound">θ</a> <a id="3771" class="Symbol">→</a> <a id="3773" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="3777" href="Algebras.Func.Congruences.html#3708" class="Bound">𝑨</a>
<a id="3779" href="Algebras.Func.Congruences.html#3688" class="Function">IsCongruence→Con</a> <a id="3796" href="Algebras.Func.Congruences.html#3796" class="Bound">θ</a> <a id="3798" href="Algebras.Func.Congruences.html#3798" class="Bound">p</a> <a id="3800" class="Symbol">=</a> <a id="3802" href="Algebras.Func.Congruences.html#3796" class="Bound">θ</a> <a id="3804" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3806" href="Algebras.Func.Congruences.html#3798" class="Bound">p</a>

<a id="Con→IsCongruence"></a><a id="3809" href="Algebras.Func.Congruences.html#3809" class="Function">Con→IsCongruence</a> <a id="3826" class="Symbol">:</a> <a id="3828" class="Symbol">{</a><a id="3829" href="Algebras.Func.Congruences.html#3829" class="Bound">𝑨</a> <a id="3831" class="Symbol">:</a> <a id="3833" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="3847" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="3849" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="3850" class="Symbol">}(</a><a id="3852" href="Algebras.Func.Congruences.html#3852" class="Bound">(</a><a id="3853" href="Algebras.Func.Congruences.html#3853" class="Bound">θ</a> <a id="3855" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="3857" href="Algebras.Func.Congruences.html#3852" class="Bound">_)</a> <a id="3860" class="Symbol">:</a> <a id="3862" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="3866" href="Algebras.Func.Congruences.html#3829" class="Bound">𝑨</a> <a id="3868" class="Symbol">{</a><a id="3869" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="3870" class="Symbol">})</a> <a id="3873" class="Symbol">→</a> <a id="3875" href="Algebras.Func.Congruences.html#3036" class="Record">IsCongruence</a> <a id="3888" href="Algebras.Func.Congruences.html#3829" class="Bound">𝑨</a> <a id="3890" href="Algebras.Func.Congruences.html#3853" class="Bound">θ</a>
<a id="3892" href="Algebras.Func.Congruences.html#3809" class="Function">Con→IsCongruence</a> <a id="3909" href="Algebras.Func.Congruences.html#3909" class="Bound">θ</a> <a id="3911" class="Symbol">=</a> <a id="3913" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="3915" href="Algebras.Func.Congruences.html#3909" class="Bound">θ</a> <a id="3917" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a>

</pre>



#### <a id="quotient-algebras">Quotient algebras</a>

In many areas of abstract mathematics the *quotient* of an algebra `𝑨` with respect to a congruence relation `θ` of `𝑨` plays an important role. This quotient is typically denoted by `𝑨 / θ` and Agda allows us to define and express quotients using this standard notation.

<pre class="Agda">

<a id="4275" class="Keyword">open</a> <a id="4280" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a> <a id="4294" class="Keyword">using</a> <a id="4300" class="Symbol">(</a> <a id="4302" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="4309" class="Symbol">;</a> <a id="4311" href="Algebras.Func.Basic.html#2960" class="Field">Interp</a> <a id="4318" class="Symbol">)</a>
<a id="4320" class="Keyword">open</a> <a id="4325" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a> <a id="4332" class="Keyword">using</a> <a id="4338" class="Symbol">(</a> <a id="4340" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="4348" class="Symbol">)</a>
<a id="4350" class="Keyword">open</a> <a id="4355" href="Function.Bundles.html#1868" class="Module">Func</a> <a id="4360" class="Keyword">using</a> <a id="4366" class="Symbol">(</a> <a id="4368" href="Function.Bundles.html#1938" class="Field">cong</a> <a id="4373" class="Symbol">)</a> <a id="4375" class="Keyword">renaming</a> <a id="4384" class="Symbol">(</a> <a id="4386" href="Function.Bundles.html#1919" class="Field">f</a> <a id="4388" class="Symbol">to</a> <a id="4391" class="Field">_⟨$⟩_</a>  <a id="4398" class="Symbol">)</a>

<a id="_╱_"></a><a id="4401" href="Algebras.Func.Congruences.html#4401" class="Function Operator">_╱_</a> <a id="4405" class="Symbol">:</a> <a id="4407" class="Symbol">(</a><a id="4408" href="Algebras.Func.Congruences.html#4408" class="Bound">𝑨</a> <a id="4410" class="Symbol">:</a> <a id="4412" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="4426" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="4428" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="4429" class="Symbol">)</a> <a id="4431" class="Symbol">→</a> <a id="4433" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="4437" href="Algebras.Func.Congruences.html#4408" class="Bound">𝑨</a> <a id="4439" class="Symbol">{</a><a id="4440" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="4441" class="Symbol">}</a> <a id="4443" class="Symbol">→</a> <a id="4445" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="4459" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="4461" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a>
<a id="4463" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="4470" class="Symbol">(</a><a id="4471" href="Algebras.Func.Congruences.html#4471" class="Bound">𝑨</a> <a id="4473" href="Algebras.Func.Congruences.html#4401" class="Function Operator">╱</a> <a id="4475" href="Algebras.Func.Congruences.html#4475" class="Bound">θ</a><a id="4476" class="Symbol">)</a> <a id="4478" class="Symbol">=</a> <a id="4480" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="4483" href="Algebras.Func.Congruences.html#4471" class="Bound">𝑨</a> <a id="4485" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="4487" href="Relations.Func.Quotients.html#2450" class="Function Operator">/</a> <a id="4489" class="Symbol">(</a><a id="4490" href="Algebras.Func.Congruences.html#3269" class="Function">Eqv</a> <a id="4494" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4496" href="Algebras.Func.Congruences.html#4475" class="Bound">θ</a> <a id="4498" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a><a id="4499" class="Symbol">)</a>
<a id="4501" class="Symbol">(</a><a id="4502" href="Algebras.Func.Basic.html#2960" class="Field">Interp</a> <a id="4509" class="Symbol">(</a><a id="4510" href="Algebras.Func.Congruences.html#4510" class="Bound">𝑨</a> <a id="4512" href="Algebras.Func.Congruences.html#4401" class="Function Operator">╱</a> <a id="4514" href="Algebras.Func.Congruences.html#4514" class="Bound">θ</a><a id="4515" class="Symbol">))</a> <a id="4518" href="Algebras.Func.Congruences.html#4391" class="Field Operator">⟨$⟩</a> <a id="4522" class="Symbol">(</a><a id="4523" href="Algebras.Func.Congruences.html#4523" class="Bound">f</a> <a id="4525" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="4527" href="Algebras.Func.Congruences.html#4527" class="Bound">a</a><a id="4528" class="Symbol">)</a> <a id="4530" class="Symbol">=</a> <a id="4532" class="Symbol">(</a><a id="4533" href="Algebras.Func.Congruences.html#4523" class="Bound">f</a> <a id="4535" href="Algebras.Func.Basic.html#4078" class="Function Operator">̂</a> <a id="4537" href="Algebras.Func.Congruences.html#4510" class="Bound">𝑨</a><a id="4538" class="Symbol">)</a> <a id="4540" href="Algebras.Func.Congruences.html#4527" class="Bound">a</a>
<a id="4542" href="Function.Bundles.html#1938" class="Field">cong</a> <a id="4547" class="Symbol">(</a><a id="4548" href="Algebras.Func.Basic.html#2960" class="Field">Interp</a> <a id="4555" class="Symbol">(</a><a id="4556" href="Algebras.Func.Congruences.html#4556" class="Bound">𝑨</a> <a id="4558" href="Algebras.Func.Congruences.html#4401" class="Function Operator">╱</a> <a id="4560" href="Algebras.Func.Congruences.html#4560" class="Bound">θ</a><a id="4561" class="Symbol">))</a> <a id="4564" class="Symbol">{</a><a id="4565" href="Algebras.Func.Congruences.html#4565" class="Bound">f</a> <a id="4567" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="4569" href="Algebras.Func.Congruences.html#4569" class="Bound">u</a><a id="4570" class="Symbol">}</a> <a id="4572" class="Symbol">{</a><a id="4573" class="DottedPattern Symbol">.</a><a id="4574" href="Algebras.Func.Congruences.html#4565" class="DottedPattern Bound">f</a> <a id="4576" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="4578" href="Algebras.Func.Congruences.html#4578" class="Bound">v</a><a id="4579" class="Symbol">}</a> <a id="4581" class="Symbol">(</a><a id="4582" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a> <a id="4587" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="4589" href="Algebras.Func.Congruences.html#4589" class="Bound">a</a><a id="4590" class="Symbol">)</a> <a id="4592" class="Symbol">=</a> <a id="4594" href="Algebras.Func.Congruences.html#3242" class="Field">is-compatible</a> <a id="4608" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4610" href="Algebras.Func.Congruences.html#4560" class="Bound">θ</a> <a id="4612" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4614" href="Algebras.Func.Congruences.html#4565" class="Bound">f</a> <a id="4616" href="Algebras.Func.Congruences.html#4589" class="Bound">a</a>

<a id="4619" class="Keyword">module</a> <a id="4626" href="Algebras.Func.Congruences.html#4626" class="Module">_</a> <a id="4628" class="Symbol">(</a><a id="4629" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a> <a id="4631" class="Symbol">:</a> <a id="4633" href="Algebras.Func.Basic.html#2875" class="Record">SetoidAlgebra</a> <a id="4647" href="Algebras.Func.Congruences.html#1468" class="Generalizable">α</a> <a id="4649" href="Algebras.Func.Congruences.html#1470" class="Generalizable">ρ</a><a id="4650" class="Symbol">)</a> <a id="4652" class="Keyword">where</a>
 <a id="4659" class="Keyword">open</a> <a id="4664" href="Algebras.Func.Basic.html#2875" class="Module">SetoidAlgebra</a> <a id="4678" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a>   <a id="4682" class="Keyword">using</a> <a id="4688" class="Symbol">(</a> <a id="4690" class="Symbol">)</a>                      <a id="4713" class="Keyword">renaming</a> <a id="4722" class="Symbol">(</a><a id="4723" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="4730" class="Symbol">to</a> <a id="4733" class="Field">A</a> <a id="4735" class="Symbol">)</a>
 <a id="4738" class="Keyword">open</a> <a id="4743" href="Relation.Binary.Bundles.html#1009" class="Module">Setoid</a> <a id="4750" href="Algebras.Func.Congruences.html#4733" class="Field">A</a> <a id="4752" class="Keyword">using</a> <a id="4758" class="Symbol">(</a> <a id="4760" href="Relation.Binary.Bundles.html#1098" class="Field Operator">_≈_</a> <a id="4764" class="Symbol">)</a> <a id="4766" class="Keyword">renaming</a> <a id="4775" class="Symbol">(</a><a id="4776" href="Relation.Binary.Structures.html#1568" class="Function">refl</a> <a id="4781" class="Symbol">to</a> <a id="4784" class="Function">refl₁</a><a id="4789" class="Symbol">)</a>

 <a id="4793" href="Algebras.Func.Congruences.html#4793" class="Function Operator">_/∙_</a> <a id="4798" class="Symbol">:</a> <a id="4800" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="4803" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a> <a id="4805" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a> <a id="4807" class="Symbol">→</a> <a id="4809" class="Symbol">(</a><a id="4810" href="Algebras.Func.Congruences.html#4810" class="Bound">θ</a> <a id="4812" class="Symbol">:</a> <a id="4814" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="4818" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a><a id="4819" class="Symbol">{</a><a id="4820" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="4821" class="Symbol">})</a> <a id="4824" class="Symbol">→</a> <a id="4826" href="Relation.Binary.Bundles.html#1072" class="Field">Carrier</a> <a id="4834" class="Symbol">(</a><a id="4835" href="Algebras.Func.Basic.html#2938" class="Field">Domain</a> <a id="4842" class="Symbol">(</a><a id="4843" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a> <a id="4845" href="Algebras.Func.Congruences.html#4401" class="Function Operator">╱</a> <a id="4847" href="Algebras.Func.Congruences.html#4810" class="Bound">θ</a><a id="4848" class="Symbol">))</a>
 <a id="4852" href="Algebras.Func.Congruences.html#4852" class="Bound">a</a> <a id="4854" href="Algebras.Func.Congruences.html#4793" class="Function Operator">/∙</a> <a id="4857" href="Algebras.Func.Congruences.html#4857" class="Bound">θ</a> <a id="4859" class="Symbol">=</a> <a id="4861" href="Algebras.Func.Congruences.html#4852" class="Bound">a</a>

 <a id="4865" href="Algebras.Func.Congruences.html#4865" class="Function">/-≡</a> <a id="4869" class="Symbol">:</a> <a id="4871" class="Symbol">(</a><a id="4872" href="Algebras.Func.Congruences.html#4872" class="Bound">θ</a> <a id="4874" class="Symbol">:</a> <a id="4876" href="Algebras.Func.Congruences.html#3354" class="Function">Con</a> <a id="4880" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a><a id="4881" class="Symbol">{</a><a id="4882" href="Algebras.Func.Congruences.html#1472" class="Generalizable">ℓ</a><a id="4883" class="Symbol">}){</a><a id="4886" href="Algebras.Func.Congruences.html#4886" class="Bound">u</a> <a id="4888" href="Algebras.Func.Congruences.html#4888" class="Bound">v</a> <a id="4890" class="Symbol">:</a> <a id="4892" href="Algebras.Func.Basic.html#3639" class="Function Operator">𝕌[</a> <a id="4895" href="Algebras.Func.Congruences.html#4629" class="Bound">𝑨</a> <a id="4897" href="Algebras.Func.Basic.html#3639" class="Function Operator">]</a><a id="4898" class="Symbol">}</a> <a id="4900" class="Symbol">→</a> <a id="4902" href="Relations.Func.Quotients.html#2708" class="Function Operator">⟪</a> <a id="4904" href="Algebras.Func.Congruences.html#4886" class="Bound">u</a> <a id="4906" href="Relations.Func.Quotients.html#2708" class="Function Operator">⟫</a><a id="4907" class="Symbol">{</a><a id="4908" href="Algebras.Func.Congruences.html#3269" class="Function">Eqv</a> <a id="4912" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4914" href="Algebras.Func.Congruences.html#4872" class="Bound">θ</a> <a id="4916" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a><a id="4917" class="Symbol">}</a> <a id="4919" href="Relation.Binary.Bundles.html#1098" class="Function Operator">≈</a> <a id="4921" href="Relations.Func.Quotients.html#2708" class="Function Operator">⟪</a> <a id="4923" href="Algebras.Func.Congruences.html#4888" class="Bound">v</a> <a id="4925" href="Relations.Func.Quotients.html#2708" class="Function Operator">⟫</a><a id="4926" class="Symbol">{</a><a id="4927" href="Algebras.Func.Congruences.html#3269" class="Function">Eqv</a> <a id="4931" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4933" href="Algebras.Func.Congruences.html#4872" class="Bound">θ</a> <a id="4935" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a><a id="4936" class="Symbol">}</a> <a id="4938" class="Symbol">→</a> <a id="4940" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="4942" href="Algebras.Func.Congruences.html#4872" class="Bound">θ</a> <a id="4944" href="Overture.Preliminaries.html#4383" class="Function Operator">∣</a> <a id="4946" href="Algebras.Func.Congruences.html#4886" class="Bound">u</a> <a id="4948" href="Algebras.Func.Congruences.html#4888" class="Bound">v</a>
 <a id="4951" href="Algebras.Func.Congruences.html#4865" class="Function">/-≡</a> <a id="4955" href="Algebras.Func.Congruences.html#4955" class="Bound">θ</a> <a id="4957" class="Symbol">{</a><a id="4958" href="Algebras.Func.Congruences.html#4958" class="Bound">u</a><a id="4959" class="Symbol">}{</a><a id="4961" href="Algebras.Func.Congruences.html#4961" class="Bound">v</a><a id="4962" class="Symbol">}</a> <a id="4964" href="Algebras.Func.Congruences.html#4964" class="Bound">uv</a> <a id="4967" class="Symbol">=</a> <a id="4969" href="Algebras.Func.Congruences.html#3139" class="Field">reflexive</a> <a id="4979" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4981" href="Algebras.Func.Congruences.html#4955" class="Bound">θ</a> <a id="4983" href="Overture.Preliminaries.html#4421" class="Function Operator">∥</a> <a id="4985" href="Algebras.Func.Congruences.html#4964" class="Bound">uv</a>

</pre>

--------------------------------------

<span style="float:left;">[← Algebras.Func.Products](Algebras.Func.Products.html)</span>
<span style="float:right;">[Homomorphisms →](Homomorphisms.html)</span>

{% include UALib.Links.md %}