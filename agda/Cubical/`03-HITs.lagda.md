```agda
{-# OPTIONS --rewriting #-} 
module `03-HITs where

open import Prelude.Paths
open GVars

open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
    renaming (_≡_ to _≣_) 
    using ()
```
# Cubical Type Theory (a review)

*AH> Because I am presenting these notes to the CLC, let's review some of the content discussed in `01-Paths.lagda.md` to refresh (or familiarize) the reader with some cubical TT basics.*

## What is homotopy type theory

Homotopy type theory, or HoTT, is principally a branch of dependent type theory concerned with:
1. A homotopical / topological interpretation of 
  - types as spaces;
  - terms as points; and
  - equalities as paths
2. exploring **univalent foundations** of mathematics

The first point requires no additional tooling beyond a standard dependent type theory (DTT), e.g., Martin-Löf Type Theory (MLTT) or the Calculus of Inductive Constructions (CIC). This point is almost aesthetic in nature: we are describing a new *vocabulary* for DTT, rather than building a new type theory. For example, an important definition in HoTT is **contractibility**:

```notAgda
is-contr : (A : Set) → Set 
is-contr A = Σ[ x ∈ A ] (∀ (y : A) → x ≡ y)
```

As a dependent type theorist, we might read this as "a type A is contractible if all of its elements are equal." As HoTT theorists, we read this as "a space A is contractible if all of its points contract to a center: that is, if every point y in the space has a path to a **center** x." In my opinion, this framework of vocabulary is quite elegant and helpful, even if you are not working with univalence (described below). For example, my own work in Agda does not invoke univalence, but nevertheless borrows definitions of contractions, propositions, sections/retractions, homotopies, and so forth. In addition, HoTT stems from an intuition that the identity type (x ≡ y) forms a **groupoid**, with refl the identity, transitivity the binary operator, and symmetry the unary operator. Accordingly, we write transitivity as _○_ and symmetry as _⁻¹. The following laws hold for all p, q, r : x ≡ y:
- p ○ refl = refl = refl ○ p
- p ○ (p ⁻¹) = p ⁻¹ ○ p = refl
- p ○ (q ○ r) = (p ○ q) ○ r 

This intuition about identity types as groupoids brings us to our secoind point---exploring **univalent foundations** of mathematics---requires the postulation of the **univalence axiom**, which states that, for types A and B in universe 𝒰, we have:

```
(A ≡ B) ≃ (A ≃ B)
```

Here _≃_ refers to an "equivalence" of types. There are a handful of equivalent definitions of equivalence, all roughly describing an isomorphism. In practice, you can assume A ≡ B means there exists f : A → B such that f has a **quasi-inverse**. A quasi-inverse is your normal definition of an inverse. Namely, f is a quasi-inverse if we have g : B → A such that 
  - f ∘ g ∼ id, and
  - g ∘ f ∼ id

where _∼_ denotes pointwise equality (or, (a homotopy*):
  - f ∼ g = ∀ (x : A) → f x ≡ g x 

What does univalence tell us? That we have functions 
- eq-eqv : (A ≡ B) → A ≃ B, and
- eqv-eq : A ≃ B → A ≡ B
and that these functions are inverse. The first definition is trivially definable by pattern matching / induction on the equality. The second requires postulation.

The intuition is that HoTT permits us to reason about types modulo isomorphism. For example, we can establish an isomorphism between the unary (ℕ) and binary (Bin) natural numbers. Under HoTT, we have that ℕ ≡ Bin, meaning a term at type ℕ can freely be cast to a Bin and vice versa. 

The groupoid interpretation of types was first established to refute the Uniqeness of Identity Principle:

```notAgda
UIP : ∀ (p q : x ≡ y) → p ≡ q
```

This principle is inherently assumed in Agda (without enabling the flag `--without-k`, but is not in-fact entailed by MLTT. What does this type mean, in practice? that `refl` need not be the only constructor of the identity type. So, types can be equal to one another in nontrivial ways. 

Consider the type Bool. With the UIP, there is one constructor of Bool ≡ Bool (that is, refl). With univalence, which is incongruent with the UIP, we also have that the isomorphism induced by `not` also induces an equality:

```notAgda
Not : Bool ≃ Bool
Not = (not , ... , ...) 

Not-≡ : Bool ≡ Bool
Not-≡ = eqv-eq Not
```

In particular, we do not have that `Not-≡ refl`. Moreover, this equality computes differently. 

```notAgda
tr : (A ≡ B) → A → B 
tr refl = id 

-- Below, we have x = true and y = false.
x y : Not-≡ 
x = tr refl true
y = tr Not-≡ true

``` 

## What does univalence give us?

On the whole, univalence has two exotic features:
- the univalence axiom
- higher inductive types

The former we just discussed; the latter we describe in this chapter.


## What is cubical type theory

HoTT has one problem: it does not compute. That is, univalence is an *axiom*, and axioms do not generally compute. Cubical type theory (or, Cubical TT) gives a *computable* and *constructive* interpretation of HoTT. This means that univalence is a **theorem**, not an axiom, and that the univalently-constructed identities compute when transporting terms.

Cubical TT achieves this firstly by reinterpreting the identity type.

## The interval type

In Cubical Agda, we have
- a type 𝕀, such that
- i₀ : 𝕀 
- i₁ : 𝕀 


## The path type

A path (x ≡ y) in cubical type theory is *not* the standard MLTT identity type. 
Rather, for x , y : A, it is a type

```notAgda 
  (x ≡ y) sort of equals (i : 𝕀) → A 
``` 

such that, given p : x ≡ y, we have 
- p i₀ = x 
- p i₁ = y 

The difference is that, while (x ≡ y) is constructed and eliminated using the syntax for functions, it is not actually a function. So we do not have that 

```notAgda
(x ≡ y) ≡ (i : 𝕀) → A
```

although one can convert between the two.


# Higher inductive types

**Higher inductive types** (HITs) are inductive types in which we specify not only *point constructors*, which generate the data of the type, but also *path constructors* which generate paths in the type. In Ch. 14 of Rijke, we are introduced to **propositional truncations**. 

## HITs via Postulates 

Because vanilla Agda lacks direct support for HITs, we were required to postulate:
- the type former `∥_∥ : Set ℓ → Set ℓ`,
- the point constructor `η : A → ∥ A ∥`, and 
- the path  constructor `α : (x y : ∥ A ∥) → x ≡ y`
of propositionally truncated types.

```agda 
module PostulatedPropTrunc where

  postulate
    ∥_∥ : ∀ {ℓ} → Set ℓ → Set ℓ 
    η : A → ∥ A ∥
    α : ∀ (x y : ∥ A ∥) → x ≣ y  
``` 

The definition of an inductive type not only describes the formation of a type and its points, but also, through pattern matching, its induction principle. In other words, an inductive type also comes with a means of its elimination, and that eliminatino will *compute definitionally*. This too we had to postulate:

```agda 
  postulate
    ∥—∥-ind : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            ((x : ∥ A ∥) → isProp (Q x)) → 
            (t : ∥ A ∥) → Q t
```

A valid question to ask is "how does one, in general, formulate the elimination condition on path constructors?" We will expore this question below.

Lastly, in order to force the induction principle to compute, we leveraged Agda's REWRITE pragma on its computational rule.

```agda
  postulate
    ∥—∥-comp : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            (p : (x : ∥ A ∥) → isProp (Q x)) → 
            ((x : A) → (∥—∥-ind f p ∘ η) x ≣ f x)
  {-# REWRITE ∥—∥-comp #-}
```


## The interval as a HIT

Cubical agda rolls the above into the object language itself, permitting a direct definition. To expore this functionality, we will begin by defining the interval type `I` as a HIT. The novelty is that we may define *path constructors* in the declaration of `I` just as we specify *point* constructors:

```agda 
data I : Set where 
    𝒾₀ : I
    𝒾₁ : I
    seg : 𝒾₀ ≡ 𝒾₁ 
``` 

## Eliminating I

Of course, as we saw via postulates, declaring I as a data type not only specifies its introduction rules, but also its elimination. Cubical Agda desirably permits elimination of I via pattern matching. We'll demonstrate with a non-trivialapplication of the interval type: namely, that it implies functional extensionality.

```agda
module FunExt {A B : Set ℓ} 
  (f g : A → B) 
  (H : f ∼ g) where
```
Note that, as `seg : 𝒾₀ ≡ 𝒾₁`, if we have `G : I → (A → B)`, then we get `ap G seg : G 𝒾₀ ≡ G 𝒾₁`; hence this will equal `f ≡ g` provided we specify that `G` sends `𝒾₀` to `f` and `𝒾₁` to `g`. 

We define `G` by pattern matching on I.

```agda
  G : I → (A → B) 
  G 𝒾₀ = f
  G 𝒾₁ = g 
```
We must also ensure that `G` is well-behaved on path constructors. In particular, that means proving that there is an inhabitant in `ap G seg : G 𝒾₀ ≡ G 𝒾₁`. As we are in cubical agda, that means producing a path from `G 𝒾₀ = f` to `G 𝒾₁ = g`.

```agda
  G (seg i) x = H x i
```

Now function extensionality is, as expected, the action of G on `seg`.

```
  fun-ext : f ≡ g 
  fun-ext = ap G seg
```

The astute reader will see that the definition `G (seg i) x = H x i` is exactly the proof of functional extensionality we derived in `01-Paths.lagda.md`.

```agda
  fun-ext′ : f ≡ g 
  fun-ext′ i x = H x i 
```

This isn't really a coincidence: when we inhabit the type `p : x ≡ y`, we (in effect) provide a term p : 𝕀 → A such that:
- p i₀ = x 
- p i₁ = y

If we view the equality (x ≡ y) as a function type (𝕀 → A), we witness an equivalence (𝕀 → A) ≃ (I → A).

```agda
  𝕀-to-I : ∀ {A : Set ℓ} → (𝕀 → A) → (I → A )
  𝕀-to-I e 𝒾₀ = e i₀
  𝕀-to-I e 𝒾₁ = e i₁
  𝕀-to-I e (seg i) = e i

  I-to-𝕀 : {A : Set ℓ} → (p : I → A) → (𝕀 → A)
  I-to-𝕀 p i = p (seg i) 
``` 

Observe that each term (p : 𝕀 → A) induces a path. While we have no "seg" path for the type 𝕀---that is, no inhabitant of i₀ ≡ i₁, since 𝕀 has its own sort---we can view the promotion of each (p : 𝕀 → A) to a path as the action of p on such a segment.

```agda
  𝕀-to-≡ : {A : Set ℓ} → (p : 𝕀 → A) → p i₀ ≡ p i₁ 
  𝕀-to-≡ p i = p i 
```

Hence we can alternatively prove `f ≡ g` by converting G to a path.

```
  I-to-≡ : {A : Set ℓ} → (p : I → A) → p 𝒾₀ ≡ p 𝒾₁
  I-to-≡ = 𝕀-to-≡ ∘ I-to-𝕀 

  _ : f ≡ g
  _ = I-to-≡ G
```

This observation induces an equivalence, which tells us---more or less---that producing an eliminator for our inductive type I is indentical to inhabiting a path type.

```agda
  𝕀-I-equiv : (𝕀 → A) ≃ (I → A) 
  𝕀-I-equiv = isoToEquiv (iso 
    𝕀-to-I 
    I-to-𝕀 
    (λ { g i 𝒾₀ → g 𝒾₀ ; g i 𝒾₁ → g 𝒾₁ ; g i (seg i₂) → ap g seg i₂ }) 
    λ _ → refl) 
```

# Propositional truncation
Let's return to propositional truncation, but cubically.

```agda
module PropTrunc where
  data ∥_∥ (A : Set ℓ) : Set ℓ where
    η : A → ∥ A ∥ 
    α : (x y : ∥ A ∥) → x ≡ y
```

We will recover (one of) the induction principle(s) as given by Rijke. but note
that the alternative condition---that Q be a family of props---
is not precisely what pattern matching will require. 

```agda
  is-prop-fam : (P : A → Set ℓ) → Set _
  is-prop-fam {A = A} P = (x : A) → isProp (P x)

  ∥—∥-ind : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            is-prop-fam Q → 
            (t : ∥ A ∥) → Q t
  ∥—∥-ind f H (η x) = f x
```

More specifically, given a path `α x y : x ≡ y`, pattern matching requires an inhabitant of `ap (∥—∥-ind f H) (α x y) : ∥—∥-ind f H x ≅ ∥—∥-ind f H y`, where the LHS has type `Q x` and the RHS has type `Q y`. So this is a dependent path type, specifically with type:


```notAgda
PathP (λ i → P (α x y i)) (∥—∥-ind f H x) (∥—∥-ind f H y)
```

The trick is to observe that, for a family of props Q, and given u : Q x and v : Q y, we have that `u` is heterogeneously equal to v. Specifically, if we transport `u` along along any equality `e : x ≡ y`, we get `v`:

```notAgda
tr Q e u ≡ v
```

This is because both `tr Q e u` and `v` are at type `Q y`, which is a proposition.

Here `∥—∥-ind f H x` has type `Q x` and `∥—∥-ind f H y` has type `Q y`, and hence there exists such a path between the two points. From there, we convert this to type `PathP` using `toPathP`, which gives us precisely the type we need.

```agda
  ∥—∥-ind {Q = Q} f H (α x y i) = p i
    where
      QPath : ∀ (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v 
      QPath u v = H y (tr Q (α x y) u) v

      p : PathP (λ i → Q (α x y i)) (∥—∥-ind f H x) (∥—∥-ind f H y)
      p = toPathP 
            {A = λ i → Q (α x y i)} 
            {x = ∥—∥-ind f H x} 
            (QPath (∥—∥-ind f H x) (∥—∥-ind f H y))

```

# Set truncation

We won't use it right now, but it will later be useful to have **set truncation**: that is, to force the type A to observe the UIP. We write ∥ A ∥₀ to indicate the set truncation of A, using the suffix _₀ to indicate the level at which A is truncated.

```agda

data ∥_∥₀ (A : Set ℓ) : Set ℓ where
  η : A → ∥ A ∥₀
  α : (x y : ∥ A ∥₀) → (p q : x ≡ y) → p ≡ q
```


# Set quotients (quotient types)

In Ch. 18 of Rijke, we described set quotients as the following encoding:

```agda 

module Rijke (A : Set ℓ) (R : A → A → Set ℓ) where
  open PropTrunc

  is-equivalence-class : (P : A → Set ℓ) → Set _
  is-equivalence-class P = ∥ Σ[ x ∈ A ] ((y : A) → P y ↔ R x y) ∥ 

  _/_ = Σ[ P ∈ (A → Set ℓ) ] (is-prop-fam P × is-equivalence-class P)
```

But this encoding can be realized more directly (and equivalently) as:

```agda
module Quotients where 
  data _/_ (A : Set ℓ) (R : A → A → Set ℓ) : Set ℓ where
    𝓆 : A → A / R 
    α : (x y : A) → R x y → 𝓆 x ≡ 𝓆 y
```

The constructor 𝓆 gives the canonical injection of an element into its equivalence class; the path constructor α asserts that elements of each equivalence class are equal.

In general, a *quotient inductive type* is a HIT that lives in Set---hence Book HoTT enforces the *Set Quotient* A / R to indeed be a quotient inductive type, via the path constructor:

```notAgda
    0-trunc : (x y : A / R) → (p q : x ≡ y) → p ≡ q 
```

We omit this, for now.

## Example: The integers

The integers may be defined as a QIT:

```agda
  module Integers where
    open import Data.Nat using (_+_)
    _≈_ : (ℕ × ℕ) → (ℕ × ℕ) → Set
    (a , b) ≈ (c , d) = a + d ≡ b + c 
    
    ℤ = (ℕ × ℕ) / _≈_
```

In other words, a pair (a , b) represents the integer a - b.

```agda
    _—_ : ℕ → ℕ → ℤ 
    a — b = 𝓆 (a , b) 

    -- canonical injection
    ι : ℕ → ℤ 
    ι n = n — 0 

    -- Proof that 3 = 5 - 2
    _ : ι 3 ≡ (5 — 2)
    _ = α (3 , 0) (5 , 2) refl 
```

Andrew can talk here, though, regarding how and why this quotient is in fact unnecessary. The gist: We can construct an idempotent function reducing pairs to one of the canonical forms (n , 0) or (0 , n):

```notAgda
  r : ℕ × ℕ → ℕ × ℕ 
  r (a , b) with a ≥? b 
  ... | yes _ = (a - b , 0)
  ... | no  _ = (0 , b - a) 
```

Hence `ℤ ≃ Σ[ x ∈ (ℕ × ℕ) ] (r x ≡ x)`. That is, the integers are in one-to-one correspondence with the fixed-points of `r`. (As `r` is idempotent, a fixed-point of `r` can be thought of as an integer already in canonical form.)

## Example: The Rationals

Another quotient: the rationals. (Don't ask me about dividing by 0.)

```agda
  module Rationals where
    open import Data.Nat using (_*_)
    _≈_ : (ℕ × ℕ) → (ℕ × ℕ) → Set
    (a , b) ≈ (c , d) = a * d ≡ b * c 

    ℚ = (ℕ × ℕ) / _≈_ 

    infixr 5 _／_
    _／_ : ℕ → ℕ → ℚ
    m ／ n = 𝓆 (m , n) 
```

Equivalent fractions are equal propositionally.

```agda
    _ : 1 ／ 2 ≡ 2 ／ 4 
    _ = α ((1 , 2)) ((2 , 4)) refl 
```

Let's observe that elimination of a rational must be, as a mathematician would say, **well-defined**. The example I recall from my math courses is:

f(a ／ b) = a 

Here the mathematician defines "well-defined" to mean "respects the equivalence relation". In particular, while we have: 

(1 ／ 2) ≈ (2 / 4)

we do not have:

f (1 ／ 2) ≡ f (2 / 4).

It's easy enough to define this for the point constructor 𝓆:
```agda
    f : ℚ → ℕ 
    f (𝓆 (n , m)) = n
```

But the path constructor requires a proof that, given
(a ／ b) ≈ (c ／ d), we have a ≡ c. This cannot be given.

```agda
    f (α (a , b) (c , d) eq i) = {!impossible!}
```

# The Circle

Finally, we will discuss the first (and last, for us!) higher inductive type with a non-trivial path.

```agda

module TheCircle where

data S¹ : Set where
  base : S¹ 
  loop : base ≡ base 

```

Following Book HoTT (Chapters 2 & 8), I declare that we Algebraic Topologists now. 

## Pointed Types

A pointed type (A , a) is a type A : 𝒰 together with a point a : A called its basepoint. We write 𝒰 ● := Σ[ A ∈ 𝒰 ] A for the type of pointed types in the universe 𝒰. Agda has level polymorphism, not universe polymorphism, so we describe the type 𝒰_{ℓ} ● as ℓ ●. 

```agda
_● : (ℓ : Level) → Set (lsuc ℓ)
ℓ ● = Σ[ A ∈ Set ℓ ] A 
```

Given a pointed type (A , a), we define the loop space of (A , a) to be the following pointed type:

```agda
Ω¹ : ℓ ● → ℓ ●
Ω¹ (A , a) = ((a ≡ a) , refl)
```

Of course, these loops may have paths between them---and so this idea may be iterated.

```agda
Ω : ℕ → ℓ ● → ℓ ●
Ω zero (A , a) = (A , a)
Ω (suc zero) (A , a) = Ω¹ (A , a)
Ω (suc n) (A , a) = Ω n (Ω¹ (A , a)) 
```

## Homotopy Groups

Given n ≥ 1 and a pointed type (A , a), we define the n'th **homotopy group** of A at a as the set truncation of Ω_{n}(A, a). 

```agda 
π : ℕ → ℓ ● → Set ℓ
π n (A , a) = ∥ (Ω n (A , a)) .fst ∥₀ 
```

Book HoTT observes:
> If (A, a) is a pointed type, then its loop space Ω (A , a) := a ≡ a has all the  structure of a group, except that it is not in general a set. It should be an ∞-group ... but we can also make it a group by truncation.

Hence set-truncation forces that the homotopy groups of A are proper groups (groups are sets).

## π₁(S¹) 

Our principle interest is in showing that π₁ (S¹ , base) ≡ ℤ. Specifically, we show that the loop space Ω¹ (S¹ , base) = (base ≡ base , refl) is equivalent to ℤ. That is, we are ignoring the set-truncation induced by π and working over the more straightforward definition given by Ω¹.

### Getting started

Boop dee boop.
