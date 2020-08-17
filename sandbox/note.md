Here's where things stand:

To finish the proof of Birkhoff, we must show

birkhoff : (K : Pred (Algebra U S)(U ⁺))
           (A : Algebra U S)
           ------------------------------------
 →         A ∈ Mod (Th (VClo K)) → A ∈ VClo K

So we need to find an algebra F : Algebra U S such that F ∈ VClo and ∃ ϕ : hom F A with ϕE : Epic ∣ ϕ ∣.

Then we can prove A ∈ VClo K using the constructor vhom F∈VClo (A , ∣ ϕ ∣ , (∥ ϕ ∥ , ϕE)), since vhom : {A : Algebra U S} → 𝑨 ∈ VClo K → ((B , _ , _) : HomImagesOf A) → B ∈ VClo K

What I have managed to prove is pretty close to this.  I proved

  Ψ⊆Kerh : Ψ{K} ⊆ KER-pred{B = ∣ A ∣} ∣ h ∣
  Ψ⊆Kerh {p , q} pΨq = hp≡hq

which says that for all equations p ≈ q such that (p , q) ∈ Ψ (i.e., all p ≈ q in Th (VClo K)), the pair (p , q) belongs to the kernel of every homomorphism h : 𝑻(X) → A.

In principle, this proves Birkhoff's theorem.

However, I believe that in order to justify the claim that we really have a constructive proof of Birkhoff's theorem, we should construct the free algebra F = 𝑻(X)/Ψ in VClo K over X and then show that there is indeed a homomorphism from F to A.

Of course, constructing F = 𝑻(X)/Ψ means constructing a quotient which, so far, I have been able to avoid by simply working with the (theoretically equivalent) homomorphic image that is isomorphic to the quotient of interest.



