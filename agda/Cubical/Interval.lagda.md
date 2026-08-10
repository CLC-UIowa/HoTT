```agda 
module Interval where 

open import Prelude.Identity

private 
  variable 
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level 
    A B C : Set ℓ 
``` 

# The Interval and Path types 

We're going to explore Cubical Agda first by describing the Interval type 𝕀 
as a HIT, using postulates. The interval type is described as a HIT such that
- i₀ : 𝕀 
- i₁ : 𝕀 
- We have a path (i₀ ≡ i₁) 

The path and interval types, in cubical type theory, are when we *really*
shift from viewing the identity type as an equality to viewing it as a *path*.
Hence we read the stipulation that i₀ ≡ i₁ not as an equality between 
the two constructors of 𝕀, but as a path between the two endpoints i₀ 
and i₁. This is analogous to the closed interval [0 , 1].

The interval type is crucial to understanding the *Path* type in Cubical Agda. 

## The interval type 
 We'll define the Interval as per 
  - Rijke, exercise 14.9
  - the HoTT book, Ch. 6, §3 

As described above, the interval is a type with two endpoints i₀ and i₁ that are connected
by a *path* `seg : i₀ ≡ i₁`.

```agda 
module Interval where 

  postulate 
      -- The interval type
      𝕀 : Set
      -- two endpoints
      i₀ : 𝕀 
      i₁ : 𝕀
      -- a non-trivial path
      seg : i₀ ≡ i₁  
``` 

### The recursion principle 

The recursion principle states that given an equality x ≡ y, we can produce a path 
from the interval 𝕀 to B. 

```agda 
      -- recursion principle
      𝕀-rec : ∀ {x y : A} (p : x ≡ y) → (𝕀 → A)
``` 

The recursor is subject to the conditions we expect of a **path**, topologically.
That is, a path p : 𝕀 → B from x to y should begin at x and end at y:
- p(i₀) = x 
- p(i₁) = y 

```agda 
      compute-𝕀-rec-i₀ : ∀ {x y : A} (p : x ≡ y) → 
                           𝕀-rec p i₀ ≡ x
      compute-𝕀-rec-i₁ : ∀ {x y : A} (p : x ≡ y) → 
                           𝕀-rec p i₁ ≡ y
      {-# REWRITE compute-𝕀-rec-i₀ compute-𝕀-rec-i₁  #-} 
``` 
Finally, we also expect that for f = 𝕀-rec p, we have f(seg) = p. That is, 
the action of f : 𝕀 → A, or (ap f) : (i ≡ j) → f i ≡ f j where i, j : 𝕀,
should have f(seg) = p. 

Recall that the condition we place on (ap f) is simply functorality. We have
an arrow i₀ ≡ i₁ in 𝕀, and so must have an arrow f i₀ ≡ f i₁ in A. As 
f i₀ = x and f i₁ = y, this is simply the arrow p : x ≡ y.

```agda       
      compute-𝕀-rec-seg : ∀ {x y : A}(p : x ≡ y) → 
                            (𝕀-rec p *) seg ≡ p
```      

The notation `_*` is pretty-syntax for `ap`---indicating that `ap` is a **map**.

### The induction principle

We have the induction principle, as expected, to be over a family P : 𝕀 → 𝒰.

``` 
  postulate 
    𝕀-ind : ∀ (P : 𝕀 → Set ℓ) (x : P i₀) (y : P i₁) → 
             (p : P ⟨ seg ⟩▸ x ≡ y) → ((x : 𝕀) → P x)
``` 

The notation `P ⟨ seg ⟩▸ x` is pretty-syntax for `tr P seg x`;
it can be read as saying we're transporting `x` along the path `seg` subject
to the type family `P`.

The induction principle f = 𝕀-ind P x y p computes as expected:
- f i₀ = x 
- f i₁ = y 
- apd f seg = p

```agda 
    compute-𝕀-ind-i₀ : ∀ (P : 𝕀 → Set ℓ) (x : P i₀) (y : P i₁) (p : P ⟨ seg ⟩▸ x ≡ y) → 
                           𝕀-ind P x y p i₀ ≡ x
    compute-𝕀-ind-i₁ : ∀ (P : 𝕀 → Set ℓ) (x : P i₀) (y : P i₁) (p : P ⟨ seg ⟩▸ x ≡ y) → 
                           𝕀-ind P x y p i₁ ≡ y   
    {-# REWRITE compute-𝕀-ind-i₀ compute-𝕀-ind-i₁  #-} 
    compute-𝕀-ind-seg : ∀ (P : 𝕀 → Set ℓ) (x : P i₀) (y : P i₁) (p : P ⟨ seg ⟩▸ x ≡ y) → 
                           apd (𝕀-ind P x y p) seg ≡ p 
``` 

## Contractibility

As per the HoTT book, "regarded purely up to homotopy, the interval is not really interesting." That is,
it is contractible. We want to show that i₀ is a center of contraction:

```agda 
  is-contr : Set ℓ → Set ℓ  
  is-contr A = Σ[ x ∈ A ] ((y : A) → x ≡ y)
  
  𝕀-contr : is-contr 𝕀 
  𝕀-contr = i₀ , f
``` 

The proof uses the induction principle for 𝕀. Specifically, we let:
- `P = (i₀ ≡_)`, so that 
- `x : i₀ ≡ i₀`, and so we let `x = refl`;
- `y : i₀ ≡ i₁`, and so we let `y = seg`;
- `p : (i₀ ≡_) ⟨ seg ⟩▸ x ≡ y`, or `p : (i₀ ≡_) ⟨ seg ⟩ refl ≡ seg`.

In other words, in order to prove `(j : 𝕀) → i₀ ≡ j`, we define an f so that:
- `f(i₀) : i₀ ≡ i₀`, so `f(i₀) = refl`
- `f(i₁) : i₁ ≡ i₁`, so `f(i₁) = seg`
- `f(seg) : (i₀ ≡_) ⟨ seg ⟩ refl ≡ seg`.

Defining the action of `f` on `seg` relies on a post-composition law for 
transports: for a, x₁, x₂ : A, p : x₁ ≡ x₂, and q : a ≡ x₁, we have 

```notAgda 
 (a ≡_) ⟨ p ⟩▸ q ≡ q ○ p
```  
Hence it follows that `(i₀ ≡_) ⟨ seg ⟩ refl ≡ refl ○ seg ≡ seg`. 

```agda 
    where  
      open PathReasoning
      f* : (i₀ ≡_) ⟨ seg ⟩▸ refl ≡ seg 
      f* = begin
        (i₀ ≡_) ⟨ seg ⟩▸ refl ≡⟨ post-comp-law i₀ _ _ seg refl ⟩ 
        refl ○ seg            ≡⟨ refl ⟩ 
        seg                   ∎
      
      f : (j : 𝕀) → i₀ ≡ j 
      f = 𝕀-ind (λ x → i₀ ≡ x) refl seg f* 
``` 

## Function extensionality

While the interval is "not interesting" in and of itself, it is alarmingly powerful.
Postulating the interval type is actually sufficient to prove functional extensionality.
The idea is to use the 𝕀 recursor to produce a function `G : 𝕀 → (A → B)` such that: 
- G i₀ = f 
- G i₁ = g
And hence, as (ap G) : (x ≡ y) → G x ≡ G y, we have:
- ap G seg : G i₀ ≡ G i₁, or: 
- ap G seg = f ≡ g

As H x : f x ≡ g x, we have 𝕀-rec (H x) : 𝕀 → B. 
Hence 𝕀-rec ∘ H : A → 𝕀 → B; flipping the arguments yields 
- G := flip (𝕀-rec ∘ H) : 𝕀 → A → B 
such that 
- G i₀ = λ x. f x 
- G i₁ = λ x. g x 

as desired. 

```agda 
  fun-ext : {f g : A → B} → f ∼ g → f ≡ g 
  fun-ext {A = A} {B = B} {f = f} {g} H = ap G seg
    where 
      G : 𝕀 → (A → B) 
      G = flip (𝕀-rec ∘ H)
``` 


