```agda
{-# OPTIONS --rewriting #-} 
module `04-HomotopyGroups where

open import Prelude.Paths
open GVars

open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
    renaming (_≡_ to _≣_) 
    using ()
```

# The Circle
```agda
module TheCircle where
```

We next discuss the first interesting HIT that is not a quotient (that is, that does not live in Set): the unit circle. We will also begin our foray into *synthetic homotopy theory* by characterizing the homotopy groups of types.

The unit circle may be defined as a point `base` and a nontrivial `loop` from `base` to `base`.

```agda
  data S¹ : Set where
    base : S¹ 
    loop : base ≡ base 
```

Critically, S¹ is not a set, as `loop` does not contract to `refl`. Let's examine this formally.

```agda
  S¹-not-set : ¬ (is-set S¹)
  S¹-not-set S = ? 
```

## Pointed Types

Following Book HoTT (Chapters 2 & 8), I declare that we Algebraic Topologists now. 

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

The question is not even: How do mathematicians make progress in mathematics? Rather, as a more explicit (and leading) form of the question, I prefer How do mathematicians advance human understanding of mathematics?

This question brings to the fore something that is fundamental and pervasive: that what we are doing is finding ways for people to understand and think about mathematics.

The rapid advance of computers has helped dramatize this point, because com- puters and people are very different. For instance, when Appel and Haken com- pleted a proof of the 4-color map theorem using a massive automatic computation, it evoked much controversy. I interpret the controversy as having little to do with doubt people had as to the veracity of the theorem or the correctness of the proof. Rather, it reflected a continuing desire for human understanding of a proof, in addition to knowledge that the theorem is true.