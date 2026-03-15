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



As an aside: I should expect `id𝔹≡ ≡ refl`. But this can't be shown as is, 
as the postulation of univalence adds a certain irreversible opacity to definitions. 

```agda
id𝔹≡refl : id𝔹≡ ≡ refl 
id𝔹≡refl with ua {A = Bool} {Bool} | is-equiv⇒equalSplits (ua {A = Bool} {Bool} .snd)
... | f , (s , sec) , r , retr | e = {!   !} 
``` 

If we instead define `id𝔹` using the other direction of univalence, it follows immediately
(as univalence is invertible) that `equivToId id𝔹′ ≡ refl`.

```agda 
idToEquiv : {A B : Set ℓ} → A ≡ B → A ≃ B
idToEquiv {A = A} {B} refl with ua {A = A} {B} 
... | f , (s , sec) , r , retr = s  refl 

id𝔹′ : Bool ≃ Bool 
id𝔹′ = idToEquiv refl 

id𝔹≡refl′ : equivToId id𝔹′ ≡ refl
id𝔹≡refl′ = ua .snd .fst .snd refl 
```

The above is quite trivial if we pick it apart: we simply define `id𝔹′` using the section of `equivToId` and it
so follows that `equivToId (idToEquiv refl) ≡ refl`. This is a bit unsatisfying, but we can use this insight,
along with an assertion that `id𝔹` really ought be the same as `id𝔹′`, to finish the deal.  


```agda
ua-is-idToEquiv-section : `sec (ua .snd) ≡ idToEquiv
ua-is-idToEquiv-section = refl

open PathReasoning 

id𝔹≡refl′′ : equivToId id𝔹 ≡ refl
id𝔹≡refl′′ = {!   !}
  -- begin
  --   equivToId id𝔹
  -- ≡⟨ refl ⟩ -- by definition of idToEquiv refl
  --   equivToId (idToEquiv refl)
  -- ≡⟨ {!  ua .snd .fst .snd refl !} ⟩ -- (λ i → (ua .snd .fst .snd) refl i) ⟩ -- using the 'f ∘ g ∼ id' homotopy
  --   refl ∎
```

## A last remark 

As another aside, I would expect that transporting along these identifications to behave more or less like the 
automorphisms from which they were constructed. For example:

```agda 
tr-id𝔹 : tr id id𝔹≡ true ≡ true 
tr-id𝔹 = {!   !} 

tr-not𝔹≡ : tr id not𝔹≡ true ≡ false 
tr-not𝔹≡ = {!   !} 
``` 

but transports only definitionally reduce when the equality witness is `refl`---recall the definition of `tr` below: 

```agda 
tr′ : {x y : A} (B : A → Set ℓ) → x ≡ y → B x → B y
tr′ B refl b = b 
``` 

I'm not sure how Rijke and/or the HOTT book rectify this. To be fair, they define transport using based path induction---
but this should incur the same problem. Typically, absent a computational interpretation like cubical agda, in which 
univalence is a theorem (not a postulate), we must augment the computational behavior of transport by adding [rewrite rules](https://agda.readthedocs.io/en/latest/language/rewriting.html)
to Agda. We will see how this gets resolved as we move on in the text (or perhaps where my assumptions go wrong).

