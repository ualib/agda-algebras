## Consolidated summary of issues raised by referees

### Review 1

1.  ~~Some paragraphs explaining specific coding choice should be expanded a bit.~~

    (done)

2.  ~~We pull some interesting bits from Abel's code; we should add some discussion (e.g. in §7) 
    of differences/similarities between our implementation and Abel's~~
   
3.  ~~In the introduction (e.g. 3rd ¶) and §2.1, we claim to take great care with foundational 
    aspects. Further explanation of the following would make clearer the relevance of our work:~~
    
    a.  ~~How does this attention to foundational details affect our coding choices?~~

    b.  ~~Whats the difference from the foundational view point between our code and work cited in Sec 7?~~

    c.  ~~At start of §2.2, our claims about setoids seem a bit bold (or "gnomic"). We don't cite work on~~
        ~~the so-called "setoid hell", and we miss the point of the bad reputation of setoids.~~
        ~~Referee asserts: setoids do not make implementation tedious, but, in a sense, unnatural~~ 
        ~~wrt informal mathematical practice, since any setoid-based reasoning depends on specific~~
        ~~implementation details. Some parts of our code (omitted from the paper) suffer from these~~
        ~~aspects of using setoids.~~
    
4.  ~~Some links are broken (e.g. in [8]); some footnotes need to have first letters capitalised.~~ (fixed)


#### Response to Review 1

*  **Point 1**  
   Discussions of coding choices were expanded.

*  **Point 2**  
   Included more details about code borrowed from Abel and adapted to suit our purposes.

*  **Point 3** (items a and b)  
   Other than 'choosing setoids', very little, for part a.  Our setup is the same as that of 
   Abel [1]. Capretta [5] uses setoids as well, but not universes since Coq doesn't "really".
   It is hard to compare with [2], since their aim and ours are quite different, but it would be useful
   to do so in the future.  Our work is strictly more general than that of [11], which also uses
   setoids, but restricts itself to finitary arities, which makes things "messy".  [14] is quite
   different, being in HoTT-UniMath, multi-sorted yet finitary.  And yet, a lot of the 'results'
   end up involving very similar statements. In other words, universal algebra seems to be quite
   foundations-independent, at some level that should be investigated in the future)

*  **Point 3** (item c)  
   The paragraph in questions, about Setoids, was rewritten to reflect the referee's constructive criticism.


### Review 2

"I have the feeling that the proofs could be simplified before, both in the article and in the formalisation."

1.  Some definitions and proofs look unnecessary and therefore lack motivation. In particular,

    *  ~~The referee says we could parameterize FreeAlgebra by a class of algebras K rather than by a 
       relation E on terms, and defines the FreeDomain F[X] as the quotient of Term X by Th K; then
       the inductive relation~~ _⊢_▹_≈_ ~~(and related proofs, soundness) are unnecessary for the proof of~~
       ~~Birkhoff to carry on.~~
       
    *  ~~Second half of the paper (starting with § on relatively free algebra) is confusing.~~
    
       ~~The reviewer was hoping for the following argument~~
       
       Define 𝔽[X] as 𝑻(X)/≈, where x ≈ y iff given any homomorphism f into an element of K, f x = f y 
       (in other words, x ≈ y iff (x,y) ∈ Th 𝒦). Then, if 𝑨 is in Mod (Th 𝒦), the surjective morphism 
       𝑻(X) → 𝑨 factors through 𝑻(X) → 𝔽[X], so it remains to show that 𝔽[X] ∈ S (P 𝒦) (then, 𝑨 ∈ HSP 𝒦). 
       
       𝔽[X] is easily shown to be a sd prod of all algebras in 𝒦. However, because of size issues, this 
       product may not exist. Fortunately, it's also a subproduct of the algebras in \{ 𝑻(X)/Θ \}, because 
       any hom factors as an epimorphism followed by a monomorphism, so that x ≈ y iff for any epimorphism 
       f into an element of S 𝒦, f x = f y.

2.  ~~Some links are broken, in particular in the footnotes~~ (https://ualib.github.io/..),
    ~~or in the bibliography item [8] (link to arxiv).~~
    
    (fixed)

3.  > The library includes a wide collection of definitions and verified
    > theorems that faithfully codify classical, set-theory-based universal
    > algebra and equational logic.

    Point out at the same time (and possibly comment further) the differences with the set-theoretic setting, 
    in particular explain how close the formalised Birkhoff theorem and proof are with respect to the 
    set-theoretic ones, especially considering
    
    *  the setoid approach;
    *  the universe hierarchy.
    
    e.g., in set theory, we consider sets and classes. As a consequence, constructing the product of all 
    algebras in S K, as in §6.2, would be forbidden because of size issues (e.g., let K be the class of all 
    algebras with empty signature).

   (A discussion section has been added for this)

4.  > ~~To the best of our knowledge, this constitutes~~
    > ~~the first machine-verified proof of Birkoff's celebrated 1935 result.~~

    ~~There is a typo in Birk[h]off. Moreover, there's a 1997 Mizar formalisation:~~
    http://www.mizar.org/JFM/Vol9/birkhoff.html ~~that we should cite in related work.~~
    ~~(though ours is still likely the first formalisation in Martin-Löf type theory)~~

    (fixed)

5.  > We are confident that the proof presented here is constructive and correct

    What made our previous formalisation contradictory and how did we fix it?


6.  > Our main contribution is the representation of algebraic structures and their
    > signatures in dependent type theory

    Can we be more specific? It seems (to the referee) our signatures are "nothing but containers."

    (Fixed. Main contribution is to show that this straightforward representation (indeed, containers)
    is quite practical.)

7.  > An environment A for X is an X indexed family of setoids

    The phrasing may seem a bit awkward; A is already introduced as an S-algebra, and an environment 
    is not *any* X-indexed family of setoids (as the sentence suggests), but rather a constant indexed 
    family of A.

8.  > Finally, we have analogous pairs of implications for P and V, called P-id1,
    > P-id2, V-id1 and V-id2, but we omit the formalizations (see [8]).

    ~~It might be worth mentioning H-id2 as well (although it is not needed).~~
    
    (done; added as suggested)

9.  > The term algebra T X is absolutely free (or initial) for algebras in the
    > signature S.

    ~~I feel that "T X is the absolutely free S-algebra on X" is better since it is
    closer to the standard terminology "T X is the free S-algebra on X".~~
    
    (done; reworded as suggested)

10.  > One approach is to let ~ be {θ ∈ Con (T X) : T X / Theta \in S K }. 
     > Equivalently, we let E = Th K and take ~ to be the least

     ~~Why is the second definition is equivalent to the first one, and what is the motivation 
     for introducing it since it doesn't seemed to be used in the formal definition. Moreover, 
     inserting the alternative definition may make the claim that F[X] is a subdirect product 
     of the algebras more confusing, since it follows obviously from the first definition and 
     not the second.~~
     
     (done; the extraneous definition was removed)

11.  > Evidently, F[ X ] is a subdirect product of the algebras in {T X / Theta },
     > where Theta ranges over congruences modulo which T X belongs to S K. Thus, 
     > F[ X ] ∈ P (S K) 

     ~~Can we detail the argument? Since F[X] is a subdirect product of algebras in S
     K, F[X] injectively embeds into a product of elements of S K, so we should expect
     F[X] ∈ S (P (S K)), rather than F[ X ] ∈ P (S K).~~
     
     (fixed; there was a missing S, as noted; also, more details are now included as requested)

12.  > Let 𝑨 ∈ 𝒦⁺; it suffices to find an algebra 𝑭 ∈ S (P 𝒦) such that 𝑨 is a
     > homomorphic image of 𝑭, as this will show that 𝑨 ∈ H (S (P 𝒦)) = 𝒦.

     Why can't we conclude the proof here by choosing 𝑭 = 𝔽[A], since we already
     showed that 𝑨 is an homomorphic image of 𝔽[A] before §6 and that 𝔽[A] ∈ S (P 𝒦) 
     (in the § on relatively free algebra in theory)?


13.  > We now define the natural epimorphism from T X onto F[ X ] and prove that its
     > kernel is contained in the collection of identities modeled by V K

     ~~Isn't it an equality rather than a mere inclusion? By definition, this kernel is
     the collection of identities modeled by K, but K and V K define the same
     collection of identities, right?~~
     
     (unchanged; it is equality, but that's not required in the proof of the HSP Theorem and, as 
     our main goal is to prove that theorem as expediently as possible, we'll leave this unchanged)

14.  > Let 𝑪 be the product of all algebras in S 𝒦, so that 𝑪 ∈ P (S 𝒦).

     Can we comment on the reason we chose a different route from the mathematical proof that we 
     describe informally? (see also: comment on the universe hierarchy).



#### Response to Review 2

*  **point 1** (bullet point 1)
   Our initial proof attempt was very similar to what the referee is suggesting. However, we switched to 
   the approach based on Setoids and requires Abel's _⊢_▹_≈_ relation because, using the former approach, 
   we could not seem to avoid introducing the inconsistency described in ¶3 of the introduction.
   
*  **point 1** (bullet point 2) and **points 12, 14**
   Finding an F in S (P K) that is the domain of an epimorphism onto an arbitrary algebra in 
   Mod (Th K) proved exceedingly difficult. It was the hardest part of the formalization of the 
   HSP theorem. The suggestions of the referee concerning this point out (correctly) that in 
   theory it's easy to show the F's they suggest are in S (P K). However, formalizing this turns 
   out to be hard. We made many, many attempts at getting all parts of the proof to work and 
   type-check, and the result presented in the paper is the most straightforward one we could 
   find.  Nonetheless, we did improve the presentation of the text surrounding the code, as 
   mentioned in the other responses, and hopefully this helps to clarify the potentially confusing 
   parts of the formalization.




### Review 3

1.  (p. 1) We mention flaws of our previous attempt. It's perplexing that we say it was a proof but 
    also say that the assumptions made lead to a contradiction. Can we explain the nature of the 
    contradiction?  How did it arise?

    More important, though we removed those assumptions, in the commented code at 
    https://ualib.org/Varieties.FreeAlgebras.html#%F0%9D%94%BD----s%F0%9D%92%A6
    we say "We will also need to assume several local function extensionality postulates and, 
    as a result, the next submodule will take as given the parameter `fe : (∀ a b → funext a b)`."
    
    Do we still need this local assumptions? If so, we need to explain.
    
    (Probably we can disregard this; I think the link is to the old version, and the comments don't 
    apply to the new version.)

2.  (p. 8) ~~aren't~~ `_IsHomImageOf_` and `epi` ~~almost synonyms? Why do we have both, why don't we define~~ 
    `_IsHomImageOf_` ~~in terms of~~ `epi`? ~~(same comment for~~ `subalgebras` and `mon`).
    
    (unchanged; yes, they are conceptually the same, so *practically* synonyms; we have both for the 
    same reason we have both in informal math; they are two sides of the same coin and one will be more 
    natural in some circumstances, and the other more natural in others)

3.  (p. 8) we say that contexts are nonempty: Why should a context be nonempty? One can get closed 
    terms by using the empty context. Do we enforce the nonemptiness condition for contexts? 
    (In the presentation it seems we don't.)

4.  (p. 9) "An environment A for X is an X indexed family of setoids." seems misleading, perhaps 
    because it's unclear whether we refer to "Environment" or to "Env".
    
    The most natural reading: we want to describe "Env" which is not an indexed family of setoids 
    but the setoid of functions with the pointwise equality.

5.  (p. 12) In the definition of `_⊢_‣_`, shouldn't `Γ` and `Δ` be mentioned as implicit parameters in the 
    clauses where they appear? 

6.  (p. 14) Why don't we define `free-lift-func` as `⟦_⟧` with `h` as the environment?

7.  (p. 14, 15) It would be informative to mention how are quotients defined in `agda-algebras`. 
    Are they obtained by changing the equivalence relation of the setoid?

8.  (p. 16) ~~It might be useful to explain (in a footnote?) what is~~ `HomReduct`

    (fixed; added a footnote to explain)

9.  (p. 17) To prove 𝒦⁺ ⊆ 𝒦 we need to construct an 𝑭 ∈ S(P 𝒦). In the paragraph explaining that 
    we start by "Let X be such that there exists a surjective environment ρ : X → U[ 𝑨 ]." 
    It seems important to explain whether we can construct such an X or if we *assume* such an X.

    (Referee's first guess: define X = Σ[ A ∈ K] U⟦ A ⟧.)

10.  (p. 17) ~~It might be useful to comment that ⊤ is the index set for showing that A is in P K.~~

     (done; added a sentence after the code clarifying this)

11.  (p. 7) ~~When we describe the compatibility condition we have an agda expression different from~~ 
     ~~the definition. Are they equivalent? The expression in the explanation is unclear. (What is~~ `(a _)`?)
     
     (fixed; added footnote to explain what the shorthand `(a _)` means)

12.  ~~(p. 10) "relative a fixed algebra..." should be "relative to a fixed algebra..."~~  (fixed)

13.  ~~(p. 17) It seems there is a missing space between~~ `...τ )` ~~and~~ `A` ~~in the definition of~~ `EqCl⇒Var` 

     (fixed; actually, no space needed after parenthesis, but we added one anyway)

14.  ~~(p. 20) The arXiv link for the reference [8] is incorrect (2101. is repeated).~~



