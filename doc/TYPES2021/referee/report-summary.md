## Consolidated summary of issues raised by referees

### Review 1

1.  Some paragraphs explaining specific coding choice should be expanded a bit.

2.  We pull some interesting bits from Abel's code; we should add some discussion (e.g. in §7) 
    of differences/similarities between our implementation and Abel's
   
3.  In the introduction (e.g. 3rd ¶) and §2.1, we claim to take great care with foundational 
    aspects. Further explanation of the following would make clearer the relevance of our work:
    
    *  How does this attention to foundational details affect our coding choices? 
    *  What is the difference from the foundational view-point between our code and other work cited in 
       sect.7? 
    *  At start of §2.2, our claims about setoids seem a bit bold (or "gnomic"). We don't cite work on 
       the so-called "setoid hell", and we miss the point of the bad reputation of setoids. Referee asserts:
       setoids do not make implementation *tedious*, but, in a sense, *unnatural* w.r.t. informal mathematical 
       practice, since any setoid-based reasoning depends on specific implementation details. Some parts of our
       code (omitted from the paper) suffer from this aspects of using setoids.

4.  ~~Some links are broken (e.g. in [8]); some footnotes need to have first letters capitalised.~~ (fixed)


### Review 2

"I have the feeling that the proofs could be simplified before, both in the article and in the formalisation."

1.  Some definitions and proofs look unnecessary and therefore lack motivation. In particular,

    *  The referee says we could parameterize FreeAlgebra by a class of algebras K rather than by a 
       relation E on terms, and defines the FreeDomain F[X] as the quotient of Term X by Th K; then
       the inductive relation _⊢_▹_≈_ (and related proofs, soundness) are unnecessary for the proof of Birkhoff
       to carry on.
       
       (The original proof did what the referee suggests, but we switched to the approach that requires 
       Abel's _⊢_▹_≈_ relation because (I think) with the former approach we ran into trouble completing
       the proof and actually introduced an inconsistency.)

    *  Second half of the paper (starting with § on relatively free algebra) is confusing.
    
       Referee suggests ("was hoping for") the following argument:
       
       Define F[X] as T X / ~, where x ~ y iff given any homomorphism f into an element of K, f x = f y 
       (in other words, x ~ y iff (x,y) ∈ Th K). Then, if A is in Mod (Th K), the surjective morphism 
       T A → A factors through T X → F[X], so it remains to show that F[X] ∈ SP K (then, A ∈ HSP K). 
       
       F[X] is easily shown to be a sd prod of all algebras in K. However, because of size issues, this 
       product may not exist. Fortunately, it's also a subproduct of the algebras in {T X / Θ}, because 
       any hom factors as an epimorphism followed by a monomorphism, so that x ~ y iff for any epimorphism 
       f into an element of S K, f x = f y.

       This argument is close to ours, but might be more understandable (provided it's correct)...?

2.  ~~Some links are broken, in particular in the footnotes~~ (https://ualib.github.io/..), ~~or in the bibliography item [8] (link to arxiv).~~ (fixed)

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

4.  > To the best of our knowledge, this constitutes
    > the first machine-verified proof of Birkoff’s celebrated 1935 result.

    There is a typo in Birk[h]off. Moreover, there's a 1997 Mizar formalisation:
    http://www.mizar.org/JFM/Vol9/birkhoff.html that we should cite in related work. 
    (though ours is still likely the first formalisation in Martin-Löf type theory)


5.  > We are confident that the proof presented here is constructive and correct

    What made our previous formalisation contradictory and how did we fix it?


6.  > Our main contribution is the representation of algebraic structures and their
    > signatures in dependent type theory

    Can we be more specific? It seems (to the referee) our signatures are "nothing but containers."


7.  > An environment A for X is an X indexed family of setoids

    The phrasing may seem a bit awkward; A is already introduced as an S-algebra, and an environment 
    is not *any* X-indexed family of setoids (as the sentence suggests), but rather a constant indexed 
    family of A.

8.  > Finally, we have analogous pairs of implications for P and V, called P-id1,
    > P-id2, V-id1 and V-id2, but we omit the formalizations (see [8]).

    It might be worth mentioning H-id2 as well (although it is not needed).

9.  > The term algebra T X is absolutely free (or initial) for algebras in the
    > signature S.

    I feel that "T X is the absolutely free S-algebra on X" is better since it is
    closer to the standard terminology "T X is the free S-algebra on X".

10.  > One approach is to let ~ be {θ ∈ Con (T X) : T X / Theta \in S K }. 
     > Equivalently, we let E = Th K and take ~ to be the least

     Why is the second definition is equivalent to the first one, and what is the motivation 
     for introducing it since it doesn't seemed to be used in the formal definition. Moreover, 
     inserting the alternative definition may make the claim that F[X] is a subdirect product 
     of the algebras more confusing, since it follows obviously from the first definition and 
     not the second.

11.  > Evidently, F[ X ] is a subdirect product of the algebras in {T X / Theta },
     > where Theta ranges over congruences modulo which T X belongs to S K. Thus, 
     > F[ X ] ∈ P (S K) 

     Can we detail the argument? Since F[X] is a subdirect product of algebras in S
     K, F[X] injectively embeds into a product of elements of S K, so we should expect
     F[X] ∈ S (P (S K)), rather than F[ X ] ∈ P (S K).

12.  > Let A ∈ K⁺; it suffices to find an algebra F ∈ S (P K) such that A is a
     > homomorphic image of F, as this will show that A ∈ H (S (P K)) = K.

     Why can't we conclude the proof here by choosing F = F[A], since we already
     showed that A is an homomorphic image of F[A] before §6 and that F[A] ∈ S P K 
     (in § on relatively free algebra in theory)?


13.  > We now define the natural epimorphism from T X onto F[ X ] and prove that its
     > kernel is contained in the collection of identities modeled by V K

     Isn't it an equality rather than a mere inclusion? By definition, this kernel is
     the collection of identities modeled by K, but K and V K define the same
     collection of identities, right?

14.  > Let C be the product of all algebras in S K, so that C ∈ P (S K).

     Can we comment on the reason we chose a different route from the mathematical proof that we 
     describe informally? (see also: comment on the universe hierarchy).



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

2.  (p. 8) aren't `_IsHomImageOf_` and `epi` almost synonyms? Why do we have both, why don't we define 
    `_IsHomImageOf_` in terms of `epi`? (same comment for `subalgebras` and `mon`).

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

8.  (p. 16) It might be useful to explain (in a footnote?) what is `HomReduct`.

9.  (p. 17) To prove `K⁺ ⊆ K` we need to construct an `F ∈ S(P(K))`. In the paragraph explaining that 
    we start by "Let X be such that there exists a surjective environment ρ : X → U[ A ]." 
    It seems important to explain whether we can construct such an X or if we *assume* such an X.

    (Referee's first guess: define X = Σ[ A ∈ K] U⟦ A ⟧.)

10.  (p. 17) It might be useful to comment that ⊤ is the index set for showing that A is in P K.


11.  (p. 7) When we describe the compatibility condition we have an agda expression different from 
     the definition. Are they equivalent? The expression in the explanation is unclear. (What is `(a _)`?)

12.  ~~(p. 10) "relative a fixed algebra..." should be "relative to a fixed algebra..."~~  (fixed)

13.  ~~(p. 17) It seems there is a missing space between~~ `...τ )` ~~and~~ `A` ~~in the definition of~~ `EqCl⇒Var` (fixed; actually, no space needed after parenthesis, but we added one anyway)

14.  ~~(p. 20) The arXiv link for the reference [8] is incorrect (2101. is repeated).~~



    
