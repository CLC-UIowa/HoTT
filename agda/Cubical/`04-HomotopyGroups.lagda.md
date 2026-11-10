```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-} 
module `04-HomotopyGroups where

open import Prelude.Paths
open import `03-HITs
open import Data.Maybe using (Maybe ; just ; nothing ; fromMaybe)
open PropTrunc
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

Critically, S¹ is not a set, as `loop` does not contract to `refl`. Let's examine this formally. (And get stuck.)

```agda
  loop≠refl : ¬ (loop ≡ refl) 
  loop≠refl p = undefined
    where 
      postulate undefined : ∀ {A : Set ℓ} → A 
      -- We have:
      --  loop i₀ = base 
      --  loop i₁ = base 
      -- And:
      --  refl i₀ = base 
      --  refl i₁ = base 
      -- So how are they different?
      K : base ≡ base → Set 
      K q = ⊥ 

      -- I want Q : base ≡ base → Bool
      -- such that:
      --   Q refl = true 
      --   Q loop = false 
      Q : S¹ → Set
      Q base = ⊥ 
      Q (loop i) = ap K p i
``` 

As you can tell, I'm stuck! 

Let's take a pit-stop and remember how to prove disjoint constructors in other cases. The usual trick is to build a large elimination from the two constructors to Set. That is, define family Q that sends true to ⊤ and false to ⊥. Then, given an equality p that true ≡ false, we have ap Q p : ⊤ ≡ ⊥. So transporting tt along this equality gives an inhabitant of ⊥.

```agda 
  dsjBool : ¬ (true ≡ false)
  dsjBool p = (ap Q p) ▸ tt 
    where 
      Q : Bool → Set
      Q true = ⊤ 
      Q false = ⊥
```

Since we have an equality p : loop ≡ refl, what we want is a family Q : (base ≡ base) → Set such that Q(loop) = ⊤ and Q(refl) = ⊥... But this contradicts the induction principle! That is, induction says that we may define Q simply by defining it on refl. 


The more nuanced take, in fact, motivates the remainder of this note. Our intuition is that the path space of S¹ is isomorphic to ℤ. That is:
```
  data ℤ : Set where 
    `_ : ℕ → ℤ 
    —_ : ℕ → ℤ  
    neg-zero : — zero ≡ ` zero

  module _ where private 
    postulate 
      eq : (base ≡ base) ≃ ℤ

```

which means we can create an equality p : (base ≡ base) ≃ ℤ 
```agda 
    p : (base ≡ base) → ℤ 
    p = ua eq ▸_ 
``` 
and it will necessarily map refl to one integer and loop to another, which we can postulate as: 

```
    postulate
      eq₀ : p loop ≡ ` zero
      eq₁ : p refl ≡ ` (suc zero)
``` 

now define `f` so that it maps negatives and zero to ⊤ and all positives to ⊥.

```
    f : ℤ → Set
    f (` zero) = ⊤
    f (— _) = ⊤
    f (` _)        = ⊥
    f (neg-zero i) = ⊤
``` 

And finally, (f ∘ p) : (base ≡ base) → Set sufficiently discriminates on refl and loop. 

```agda  
    S¹-not-set : ¬ (isSet S¹)
    S¹-not-set σ = bad ▸ tt 
      where 
        bad : ⊤ ≡ ⊥ 
        bad = (ap f eq₀ ⁻¹) ○ (ap (f ∘ p) (σ base base loop refl) ○ (ap f eq₁)) 
``` 

Of course, this crucially relies on the computational content of the postulate `eq : (base ≡ base) ≃ ℤ`. That is: univalence must give us an equivalence that maps refl and loop to separate integers. 

We next build such an equivalence via the fundamental group of S¹.


## Pointed Types

Following Book HoTT (Chapters 2 & 8), I declare that we Algebraic Topologists now. 

A pointed type (A , a) is a type A : 𝒰 together with a point a : A called its basepoint. We write 𝒰 ● := Σ[ A ∈ 𝒰 ] A for the type of pointed types in the universe 𝒰. Agda has level polymorphism, not universe polymorphism, so we describe the type 𝒰_{ℓ} ● as ℓ ●. 

```agda
  _● : (ℓ : Level) → Set (lsuc ℓ)
  ℓ ● = Σ[ A ∈ Set ℓ ] A 
```

Given a pointed type (A , a), we define the loop space of (A , a) (as per Def 2.1.8 of Book HoTT) to be the following pointed type:

```agda
  Ω¹ : ℓ ● → ℓ ●
  Ω¹ (A , a) = ((a ≡ a) , refl)
```
That is, if A is pointed, then the type of loops on a is (a ≡ a), and this type too is pointed via refl. Note that, in other places, the loop space of (A, a) is more simply just (a ≡ a). But such a definition is ill-typed---below, we define the n-fold iterated loop space Ωⁿ(A , a) as a function from pointed types to pointed types, and so Ω¹(A , a) must be a pointed space. (We could have alternatively defined Ω : ℕ → ℓ ● → Set ℓ, but why would we want to...)

I am concerned, nonetheless, as I thought e.g. (S¹ , base) should have a loop space centered on (base ≡ base, loop). We will see how this plays out.


```agda
  Ω : ℕ → ℓ ● → ℓ ●
  Ω zero (A , a) = (A , a)
  Ω (suc n) (A , a) = Ω n (Ω¹ (A , a)) 

  Ω⁰ Ω² Ω³ : ℓ ● → ℓ ●
  Ω⁰ = Ω 0
  Ω² = Ω 2
  Ω³ = Ω 3
  {-# DISPLAY Ω 0 x = Ω⁰ x #-}
  {-# DISPLAY Ω 2 x = Ω² x #-}
  {-# DISPLAY Ω 3 x = Ω³ x #-}
```

## Homotopy Groups

Given n ≥ 1 and a pointed type (A , a), we define the nᵗʰ **homotopy group** of A at a as the set truncation of Ω_{n}(A, a). 

```agda 
  π : ℕ → ℓ ● → Set ℓ
  π n (A , a) = ∥ (Ω n (A , a)) .fst ∥₀ 
```

Book HoTT observes:
> If (A, a) is a pointed type, then its loop space Ω (A , a) := a ≡ a has all the  structure of a group, except that it is not in general a set. It should be an ∞-group ... but we can also make it a group by truncation.

Hence set-truncation forces that the homotopy groups of A are proper groups (groups are sets).

## π₁(S¹) 

Our principle interest is in showing that π₁ (S¹ , base) ≡ ℤ. Of course, 

```no
  π₁(S¹, base) 
= ∥ Ω 0 (Ω¹ (S¹ , base)) ∥ 
= ∥ (Ω¹ (S¹ , base)) ∥ 
= ∥ (base ≡ base , refl) ∥ 
``` 
and so if we prove the stronger claim that the loop space of (S¹, base) is isomorphic to ℤ, it follows that π₁(S¹, base) is a set, as ℤ is a set and isomorphisms preserve sets. Hence we will have shown that, by congruence,
that π₁(S¹, base) ≡ ∥ ℤ ∥ ≡ ℤ.

### Getting started

We must define an isomorphism between (base ≡ base, refl) and ℤ. In the backwards direction, map zero to refl, positives p to loop⁺ p, and negatives to loop⁻ p. (We have to map positives and negatives separately to convince Agda that loopⁿ is well-founded.)

```agda 
  module NaiveApproach where
    loopⁿ : ℤ → base ≡ base 
    loop⁺ : ℕ → base ≡ base 
    loop⁻ : ℕ → base ≡ base 
``` 

loop⁺ n yields n iterations of loop, that is:

refl ○ loop ○ loop ○ ... loop
       {---------------------}
          n loops 


loop⁻ n yields n iterations of loop ⁻¹, that is:

refl ○ loop⁻ ○ loop ⁻¹ ○ ... loop⁻
       {---------------------}
          n loop⁻¹s

```agda
    loop⁺ zero = refl
    loop⁺ (suc n) = loop⁺ n ○ loop

    loop⁻¹ = loop ⁻¹
    loop⁻ zero = refl
    loop⁻ (suc n) = loop⁻ n ○ loop⁻¹


    loopⁿ (` n) = loop⁺ n
    loopⁿ (— n) = loop⁻ n
    loopⁿ (neg-zero i) = eq i
      where 
        eq : loopⁿ (` zero) ≡ loopⁿ (— zero)
        eq = refl 
``` 

Defining a function in the other direction---from loops to ℤ---is a bit trickier, but very possible!

Observe that succ is an equivalence: indeed, its inverse is pred. In our case, we have defined ℤ, effectively, as ℕ + ℕ with a quotient over zero. That is: we have neither a successor nor predecessor constructor. But we can make do. 

Define a successor function like so: 

```agda 
    succ : ℤ → ℤ 
    succ (` n) = ` (suc n)
    succ (— zero) = ` 1
    succ (— suc n) = — n
    succ (neg-zero i) = eq i 
      where 
        eq : succ (` 0) ≡ succ (— 0)
        eq = refl 
``` 

And a predecessor like so: 

```agda 
    pred : ℤ → ℤ 
    pred (` zero) = — 1
    pred (` suc n) = ` n
    pred (— n) = — (suc n)
    pred (neg-zero i) = eq i 
      where 
        eq : pred (` 0) ≡ pred (— 0)
        eq = refl 
``` 

Now, before we define an equivalence on ℕ via suc, we'll need an important fact: our integers best be a set. The simplest way to show this is to exhibit that ℤ has decidable equality---by Hedberg's theorem, it is then a set.

```agda 
    discreteℤ : Discrete ℤ
    discreteℤ (` x) (` x₁) = {! _≟_  !}
    discreteℤ (` x) (— x₁) = no {!   !}
    discreteℤ (` x) (neg-zero i) = {!   !}
    discreteℤ (— x) (` x₁) = {!   !}
    discreteℤ (— x) (— x₁) = {!   !}
    discreteℤ (— x) (neg-zero i) = {!   !}
    discreteℤ (neg-zero i) (` x) = {!   !}
    discreteℤ (neg-zero i) (— x) = {!   !}
    discreteℤ (neg-zero i) (neg-zero i₂) = {!   !} 

    ℤ-set : isSet ℤ 
    ℤ-set = Discrete⇒isSet discreteℤ 
``` 

```agda
    Suc :  ℤ ≃ ℤ
    Suc = isoToEquiv (iso succ pred σ ρ)
      where 
        σ : section succ pred
        σ (` zero) = neg-zero
        σ (` suc n) = refl
        σ (— n) = refl
        σ (neg-zero i) = eq i 
          where 
            eq : PathP (λ i → — 0 ≡ (neg-zero i)) (σ (— 0)) (σ (` 0))
            eq j = {!  !} 

        ρ : retract succ pred 
        ρ = {!   !} 
```     