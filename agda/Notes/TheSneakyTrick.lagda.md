# The g(x) ⁻¹ ○ g(y) trick

In a few places (e.g., HoTT book Lemma 3.3.4, or Rijke's Theorem 10.2.3) we use
a trick to prove that some equality `x ≡ y` equals refl. The use of this trick
is "very HoTT", because it's a proof about paths---the sort of thing one doesn't
need to do with axiom K (and hence most of regular Agda work).

## Examples

One instance is in a proof that the contraction of a center equals refl. Or, more accurately,
given a contraction `C`,  we can construct a contraction `C′` such that `C` applied to the center
equals refl.

```agda
module Notes.TheSneakyTrick where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`10.Reading
open import Chapters.`11.Reading

private variable
  ℓ : Level 
  A : Set ℓ

module _ (cntr : is-contr A) where
  open is-contr cntr renaming (center to a ; contraction to C)
  -- "WLOG, we may assume that C comes equipped with an
  -- identification p : C(a) ≡ refl." If it does not,
  -- we can construct a new contraction C′ s.t.
  -- C′(a) ≡ refl:
  C′ : (x : A) → a ≡ x
  C′ x = (C a) ⁻¹ ○ C x

  p : C′ a ≡ refl
  p = left-inv (C a)  
```

The nuance of the proof is that `C` is arbitrary, but we'd sure like `C(a)`
to equal refl. So we define `C′` as *post-composition by a*, and show
that `C′(a) ≡ refl`. `C′(a)` is definitionally a contraction.

What is going on here? Note that `C(a) : a ≡ a` is opaque: given no other
information about `A`, we cannot assert that `C(a) ≡ refl`. (Doing so would be
precisely an invokation of axiom K!). However, we do know that A is contractible, so
we can construct `C′(a) = C(a) ⁻¹ ○ C(a) : a ≡ a`. Another proof of `a ≡ a`, but
this time we know by the groupoid structure of identity types that `C′(a)` is
propositionally equal to refl.

The second example shows up in the HoTT book Lemma 3.3.4 when showing that
every proposition is a set. 

```
open import Chapters.`12.Reading hiding (Irrelevant⇒UIP)

Irrelevant⇒UIP : Irrelevant A → UIP A
Irrelevant⇒UIP {A = A} isProp x y p q = lem x y p ○ (lem x y q) ⁻¹
  where
    g : (z : A) → x ≡ z
    g z = isProp x z
    lem : ∀ (a b : A) (p : a ≡ b) → p ≡ (g a) ⁻¹ ○ g b
    lem a b refl = (left-inv (g a)) ⁻¹
```

Here the challenge is that we want to prove that `p ≡ q` where `p q : x ≡ y`.
The lemma we use states that any proof of `a ≡ b` must equal `g(a) ⁻¹ ○ g(b)`
where `g` is post-composition by `x`. Observe that `g` is really a
*contraction*, as before: it says that `x` is a center, and all `(z : A)` are
equal to the center `x`. (Nevermind for the moment that `A` isn't
*contractible*; the center `x` is *assumed* as an argument). Pictorially,
if `A` is contractible with center `a : A`, and `x, y : A` with proofs `p , q :
x ≡ y`, then we are asserting that the following diagram commutes.

----------------------------
lem:
----------------------------
            a
  g(x)̂¹ /     \  g(y)
       /        \ 
     /   p , q   \ 
    x ----------- y 
----------------------------

This commutativity seems to hold provided `g` is constructible (that is, `A` has a contraction).
Generalizing to a helper-lemma:

```agda
module _ (cnt : is-contr A) where
  open is-contr cnt renaming (center to a ; contraction to C)

  contractionLoop : ∀ (x y : A) (p : x ≡ y) → p ≡ (C x) ⁻¹ ○ C y
  contractionLoop _ _ refl = left-inv (C _) ⁻¹ 
```

This seems to be the essence of the proof trick. Other properties fall away trivially, e.g.:

```


  K : Axiom-K A
  K x p = contractionLoop x x p ○ left-inv (C x) 
```


