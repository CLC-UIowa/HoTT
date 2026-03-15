```
module Notes.OnEquivalence where

open import Chapters.`09.Reading hiding (is-equiv; has-inverse ; is-equiv⇒equalSplits)
open import Chapters.`10.Reading hiding (is-contr-map; is-coh-invertible)
open import Prelude

private variable
  ℓ : Level
  A B C D : Set ℓ
```

# Some notes on type equivalence

Chapters 9 and 10 are concerned with notions of equivalence between types.
I'm writing this note to (i) disambiguate mixed terminology in HOTT texts, and
(ii) explain (to myself and you) the confusing need for *four* separate notions
of type equivalence.


## Bi-invertible maps, or "equivalences"

In chapter 9, we introduced "bi-invertible maps" as a notion of type
equivalence:

```agda
is-equiv : (f : A → B) → Set _
is-equiv f = section f × retraction f
```

that is, f is a bi-invertible map if it has both a section and retraction. Rijke additionall
calls f an "equivalence", as it witnesses an equivalence A ≃ B between the types A and B.
Inhabiting is-equiv f amounts to specifying two additional functions---a section of f, call it h,
such that 

  f ∘ h ∼ id

and a retraction of f, call it g, such that 

  g ∘ f ∼ id.

**Terminology.** fortunately, Rijke and the HOTT book agree on the term
"bi-invertible map" to describe functions with both sections and equivalences;
the HOTT text does not call such maps "equivalences" and indeed reserves the
term "is-equiv f" to (first) vaguely describe the idealized definition of type
equivalence, and (later) defines "is-equiv f" to mean that f is a half-adjoint
equivalence.


## Quasi-inverses

In the definition of bi-invertible maps, it's clear that one of h or g are
redundant: if f has both a section and retraction, then the two are
(homotopically) equivalent.

```agda
module _ where 
  open HomReasoning
  is-equiv⇒equalSplits : ∀ {f : A → B} (p : is-equiv f) → `sec p ∼ `retr p
  is-equiv⇒equalSplits {f = f} ((g , G) , (h , H)) = begin
    g          ∼⟨ (H ·ᵣ g) ⁻¹ ⟩
    h ∘ f ∘ g  ∼⟨ h ·ₗ G ⟩
    h ∎
```


In other words, we really ought not need to specify both, leading to the more
standard definition: the function f "has an inverse" if there exists g : B → A
such that

  f ∘ g ∼ id 

and 

  g ∘ f ∼ id.

```agda
has-inverse : (A → B) → Set _
has-inverse {A = A} {B = B} f = Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) × (g ∘ f ∼ id)
```

It's straightforward to show that the types `is-equiv f` and and `has-inverse f`
imply eachother, and so are logically equivalent. The more pertinent questions
is why we bother with any definition besides has-inverse?


Rijke writes, on why we have both the definitions `is-equiv` and `has-inverse`,
that:

> We did not define equivalences to be functions that have inverses. The reason
> is that we would like that being an equivalence is a _property_, not a
> non-trivial structure on the map f. This fact requires the function
> extensionality axiom, but we can already say that if a map f is an
> equivalence, then it has up to homotopy only one section and only one
> retraction.
>
> The type `has-inverse f` on the other hand, turns out to be
> homotopically complicated.  In exercise 22.5, we will see that the identity
> function idₛ¹ : S¹ → S¹ on the circle is an example of a map for which
>  has-inverse idₛ¹ ≃ ℤ.

The HOTT text likewise asserts that the definition `has-inverse` is ill-behaved.

> When doing proof-relevant mathematics, the corresponding type [of
> `has-inverse`] is poorly behaved. For instance, for a single function f : A →
> B there may be multiple unequal inhabitants of `has-inverse f`. (This is
> closely related to the observation in higher category theory that often one
> needs to consider adjoint equivalences rather than plain equivalences.) FOr
> this reason, we give [`has-inverse f`] the following historically accurate,
> but slighlty derogatory-sounding name "quasi-inverse".


**Terminology.** As just described, The HOTT uses the term "quasi-inverse".

## Contractible maps

Perhaps the most elegant (yet least ergonomic) definition is of contractible
maps: a function f witnesses an equivalence if all of its fibers are
contractible. Put set theoretically (or, perhaps topologically?): f is
invertible iff all of its fibers are singletons. (This is a terse way
of saying f is both injective and surjective.)

```agda
is-contr-map : (f : A → B) → Set _
is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b)
```

While elegant, inhabiting `is-contr-map f` can be less intuitive and more elaborate 
than inhabiting the more standard `has-inverse f`. 

It can be shown more broadly that:

  is-equiv f ⇔ has-inverse f ⇔ is-contr-map f ⇔ is-coh-invertible f 

(with `is-coh-invertible f` defined below), and hence in practice we are permitted 
to produce a witness to `has-inverse f` instead. 


## Half-adjoint equivalences / coherently-invertible maps

Finally, we define coherently invertible maps as maps with inverses and an additional
coherence property.

```
record is-coh-invertible (f : A → B) : Setω where
  field
    g′ : B → A
    G-hom : f ∘ g′ ∼ id
    H-hom : g′ ∘ f ∼ id
    K-hom : G-hom ·ᵣ f ∼ f ·ₗ H-hom
```

Why the extra homotopy? I suspect this additional homotopy
is what's necessary to make `is-coh-invertible f` a mere proposition. That is,
for any two inhabitants of `is-coh-invertible f` to be propositionally equivalent. 
Below we outline this property as a desirable condition of type equivalence.


**terminology.** The HOTT book defines coherently invertible maps as 
"half adjoint equivalences", a term borrowed from higher category theory.
  
> Def. 4.2.1 (§4.2, pp 173): A function f : A → B is a *half adjoint equivalence*
> if there are g : B → A and homotopies η : g ∘ f ∼ id and ϵ : f ∘ g ∼ id such that
> there exists a homotopy 
>   τ : Π(x : A) f (η x) = ϵ (f x)


## A table of mixed terminology

The following table summarizes the terms used by the HOTT book and Rijke.

| Rijke | HOTT | Name in Agda | Meaning |
| ------------- | ------------- | ------------- | ------------- |
| Bi-invertible map / equivalence | bi-invertible map | `is-equiv f` | `f` has a section and a retraction |
| "has an inverse" | quasi-inverse | `has-inverse f` | `f` has left and right inverse `g` |
| contractible map | contractible map | `is-contr-map f` | `f` has contractible fibers |
| coherently invertible map | half adjoint equivalence | `is-coh-invertible f` | `f` has a left and right inverse `g` and an additional homotopy (see def'n) |


## Which definition is the best?

What is it, then, we are looking for? The HOTT text (§2.4) provides a specification.

> We will reserve the word _equivalence_ for an improved notion isequiv(f) with the following properties:
> - For each f : A → B, there is a function qinv(f) → isequiv(f)
> - Similarly, for each f we have isequiv(f) → qinv(f); thus the two are logically equivalent.
> - For any two inhabitants e₁, e₂ : isequiv(f) we have e₁ = e₂

We define an "equivalence" isequiv(f) to mean
a function logically equivalent to a quasi-inverse (i.e., of having an inverse),
but with the additional property that isequiv(f) is a *mere proposition*: any two
inhabitants are equal. That is: 

  ∀ f. is-prop (isequiv f).

We finally define type equivalence as

  A ≃ B := Σ[ f ∈ A → B ] (isequiv f).

What then is `isequiv f`? Three out of four definitions satisfy the criteria
above: bi-invertible maps (Rijke's `is-equiv f`), contractible maps, and
half-adjoint equivalences are each pairwise equivalent *and* each mere
propositions.  Certain sources, such as [1lab](1lab.dev), choose to define
isequiv as a contractible map. The HOTT text chooses half-adjoint equivalences.


The first two conditions---that isequiv(f) be logically equivalent to qinv(f)---
are sensible, ergonomic requirements: inhabiting qinv(f) is most typical and requires
the least mental gymnastics. Why the necessity that isequiv(f) be a mere proposition?
The shortest answer is that this "plays nicely" with univalence. To dive deeper, we have
to remember that, in the _univalent foundations of mathematics_, univalence is assumed
as an _axiom_. Univalence can be postulated as follows:

```agda
postulate
  ua : (A ≃ B) ≃ (A ≡ B) 

-- left to right direction (the opposite direction is immediate)
equivToId : A ≃ B → A ≡ B 
equivToId eq = ua .fst eq 
```

The moral of this story might be to be careful what you "wish" for. Requiring that isequiv(f)
be a mere proposition prevents logical conundrums to follow from univalence. The easiest example
I can think of is the identifications of Booleans. Recall that bools have precisely two automorphisms: 
one induced by the identity mapping and one induced by negation.

```agda 
id𝔹 not𝔹 : Bool ≃ Bool
id𝔹 = id , ((id , refl-∼) , (id , refl-∼)) 
not𝔹 = not , ((not , neg-bool-id) , (not , neg-bool-id))
``` 

With univalence in hand, we can produce two distinct identifications of Bool. 

```agda 
id𝔹≡ not𝔹≡ : Bool ≡ Bool 
id𝔹≡ = equivToId id𝔹 
not𝔹≡ = equivToId not𝔹
```

These are the *only* two distinct identifications of Bool. Permitting isequiv(f) 
to not be a mere proposition can become hazardous. Suppose, for example,
that we have two distinct proofs that `not` forms an equivalence on `Bool`. 
```agda
postulate
  not-equiv₁ not-equiv₂ : is-equiv not
``` 


Now two distinct equivalences can be formed from the same map `not`. 

```agda 
not𝔹₁ not𝔹₂ : Bool ≃ Bool
not𝔹₁ = not , not-equiv₁ 
not𝔹₂ = not , not-equiv₂ 
``` 

Likewise, we have extra distinct identifications:

```agda 
not𝔹₁≡ not𝔹₂≡ : Bool ≡ Bool 
not𝔹₁≡ = equivToId not𝔹₁
not𝔹₂≡ = equivToId not𝔹₂
``` 

Of course, that `is-equiv not` is a mere proposition means `not-equiv₁` and `not-equiv₂` are equal, and hence the identifications `not𝔹₁≡` and `not𝔹₂≡` collapse together. This property explains why we do not choose `has-inverse f` as a suitable definition of equivalence, as `has-inverse f` is not a mere proposition. 

Had we chosen to define isequiv(f) as the predicate `has-inverse f` lands us in the uncomfortable scenario described above, as e.g. 
`idₛ¹ : S¹ → S¹` on the circle is an example of a map for which `has-inverse idₛ¹ ≃ ℤ`.
I can't speak immediately to the hazards of this scenario (that is, what goes catastrophically wrong as a result), 
other than the hazard of being incorrect. 


### The computational content of univalence

As an aside: I should expect `id𝔹≡ ≡ refl`. But this can't be shown quite yet, as 
postulating univalence in the fashion we have has added a certain irreversible opacity to definitions. Below 
I tinker but get nowhere. 

```agda
id𝔹≡refl : id𝔹≡ ≡ refl 
id𝔹≡refl with ua {A = Bool} {Bool} | is-equiv⇒equalSplits (ua {A = Bool} {Bool} .snd)
... | f , (s , sec) , r , retr | e = {!   !} 
``` 

Our problem is that the postulate `ua` has a section `s : A ≡ B → A ≃ B`. But this direction is totally definable! So the cart and horse are backwards. It is more fruitful to define univalence by first defining the identity-to-equivalence direction and then postulating it is an equivalence. This leaves the axiomatic direction (that equivalences yield identifications) opaque, but lends computational content to the trivial direction. 

```agda 
idToEquiv : A ≡ B → A ≃ B 
idToEquiv refl = id , (id , refl-∼) , (id , refl-∼) 

postulate 
  univalence : is-equiv (idToEquiv {A = A} {B})

ua′ : (A ≡ B) ≃ (A ≃ B) 
ua′ = idToEquiv , univalence 

equivToId′ : A ≃ B → A ≡ B 
equivToId′ e = `sec univalence e
``` 

Now it follows definitionally that `id𝔹 ≡ idToEquiv refl`. (N.b., as `is-equiv` is a mere proposition, 
this statement holds for *any* definition of `id𝔹` in which the first component is `id`. In other words, we are not simply relying
on the inhabitants of `is-equiv id` lining up by coincidence.)

```agda
_ : id𝔹 ≡ idToEquiv refl 
_ = refl 
``` 


## The computational content of transport (A last remark)

As another aside, I would expect that transporting along these identifications to behave more or less like the automorphisms from which they were constructed. For example:

```agda 
tr-id𝔹₀ : tr id (equivToId′ id𝔹) true ≡ true 
tr-id𝔹₀ = {!   !} 

tr-not𝔹₀ : tr id (equivToId′ not𝔹) true ≡ false 
tr-not𝔹₀ = {!   !} 
``` 

but transports only definitionally reduce when the equality witness is `refl`---recall the definition of `tr` below: 

```agda 
tr′ : {x y : A} (B : A → Set ℓ) → x ≡ y → B x → B y
tr′ B refl b = b 
``` 

One attempt to lend computational content to these transports is *cubical Agda* (stemming from *cubical type theory* more broadly, e.g., [Cohen, et al](https://www.cse.chalmers.se/~coquand/cubicaltt.pdf)). While it *is* the case that univalence is a *theorem* in cubical type theory, not an axiom, great lengths must be taken in order to ensure that transports reduce properly. In particular, I recall that the computational behavior of `transport` depends on the _type_ of the inputs. The machinery involved (something called glue?) gets intricate quite quickly, and there are other (frankly inhospitable) aspects to cubical agda---for example, identities are literal paths out of the unit interval, and so inhabiting paths between paths requires solving a system of "edge condition" equations. Thinking in this manner is taxing and unintuitive. (If, despite this, you remain interested, I recommend [1lab.dev](https://1lab.dev/1Lab.Path.html#path) and [cubical agda](https://agda.readthedocs.io/en/latest/language/cubical.html) as further reading.)

The other route, which I anticipate we will see in Rijke, is to simply postulate the computational behavior of transports along univalently constructed identities. As so: 

```agda 
transport : A ≡ B → A → B 
transport = tr id 

postulate 
  ua-β : (e : A ≃ B) (x : A) → transport (equivToId′ e) x ≡ e .fst x 
```

The postulate `ua-β` quite literally asserts that transporting along an identity constructed by an equivalence is the application of that equivalence.
Returning to our goals above: 

```agda
tr-id𝔹 : tr id (equivToId′ id𝔹) true ≡ true 
tr-id𝔹 = ua-β id𝔹 true 

tr-not𝔹≡ : tr id (equivToId′ not𝔹) true ≡ false 
tr-not𝔹≡ = ua-β not𝔹 true 
``` 

To conclude with one final remark: The definitions of `is-equiv` and `_≃_` as nested Σ-types becomes 
cumbersome very quickly; I would recommend we replace these (that is, the definitions `is-equiv`, `_≃_`, `section`, and `retraction`) with records for easier bookkeeping. 
