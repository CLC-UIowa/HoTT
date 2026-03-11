```
module Notes.OnEquivalence where

open import Chapters.`09.Reading hiding (is-equiv; has-inverse ; is-equiv⇒equalSplits)
open import Chapters.`10.Reading hiding (is-contr-map; is-coh-invertible)
open import Prelude
open HomReasoning

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

```
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

```
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

```
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
invertible iff all of its fibers are singletons. (This sentence is a terse way
of saying f is both injective and surjective.)

```
is-contr-map : (f : A → B) → Set _
is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b)
```

It can be shown that:

  is-equiv f ⇔ has-inverse f ⇔ is-contr-map f


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

Why the extra homotopy? While I've not proven it, I suspect this additional homotopy
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

To couch this in Rijke's parlance, we define an "equivalence" isequiv(f) to mean
a function logically equivalent to a quasi-inverse (i.e., of having an inverse),
but with the additional property that isequiv(f) is a *mere proposition*: any two
inhabitants are equal. That is,

  ∀ f. is-prop (isequiv f).

We finally define type equivalence as

  A ≃ B := Σ[ f ∈ A → B ] (isequiv f).

What then is `isequiv f`? Three out of four definitions satisfy the criteria
above: bi-invertible maps (Rijke's `is-equiv f`), contractible maps, and
half-adjoint equivalences are each pairwise equivalent *and* each mere
propositions.  Certain sources, such as [1lab](1lab.dev), choose to define
isequiv as a contractible map. The HOTT text chooses half-adjoint equivalences.

I am not precisely sure what it's crucial that equivalence be a mere proposition
outside of the personal experience that propositional irrelevance can be nice
(if not crucial) to have. But at this time I can't point to a particular proof or result
that relies on this irrelevance.


