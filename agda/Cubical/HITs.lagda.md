```agda
module HITs where

open import Prelude.Paths
```

# The interval as a HIT

In ./Postulate.lagda.md, we explored the interval type as a postulated higher inductive type.
Now, for the first time, we will explore it as a HIT in *cubical Agda*, which allows a direct
definition. Note that the cubical library / flag permit the definition of **path constructors**
directly on I!


```agda 
data I : Set where 
    𝒾₀ : I
    𝒾₁ : I
    seg : 𝒾₀ ≡ 𝒾₁ 
``` 

## The recursion/induction principle

Let's first observe that pattern matching on I produces the desired recursion and
induction principles, and that these compute definitionally.

```agda
I-ind : ∀ {ℓ} (P : I → Set ℓ) (x : P 𝒾₀) (y : P 𝒾₁) → 
          (p : PathP (λ i → P (seg i)) x y) → ((i : I) → P i)
I-ind P x y p 𝒾₀ = x
I-ind P x y p 𝒾₁ = y
```
Critically, we have that pattern matching on 𝒾 : I also produces
an obligation to produce a term M at type P (seg j) for j : I subject
to the boundary conditions:
- M = x when j = i₀ 
- M = y when j = i₁ 

Let's first remark upon the insight this gives us regarding the
"general form" of elimination of a path constructor in cubical
type theory. Recall that the goal, when defining 
- f = I-ind P x y p : ((i : 𝕀) → P i)
is to map f over the arrow seg : 𝒾₀ ≡ 𝒾₁ to an arrow 
ap f seg : f 𝒾₀ ≡ f 𝒾₁. Of course, f 𝒾₀ : P 𝒾₀ and 
f 𝒾₁ : P 𝒾₁ are at different types, and so we can't equate f 𝒾₀ and f 𝒾₁ with 
a homogeneous path. We instead have a *dependent* path:

```notAgda
ap f seg : PathP (P ∙ seg) (f 𝒾₀) (f 𝒾₁)
```

Further, f 𝒾₀ = x and f 𝒾₁ = y definitionally.
Hence we see that, a term M : (j : 𝕀) → P (seg j)
subject to the boundary conditions 
- M i₀ = f 𝒾₀ = x 
- M i₁ = f 𝒾₁ = y
is precisely the arrow of type ap f seg we are looking for.

In other words: when defining f by pattern matching over
a HIT, we are required to ensure that ap f e is well-defined
and well-typed for each path constructor e.

```
I-ind P x y p (seg j) = p j  
```

## I is contractible 

As an exercise, we can prove that I is contractible, this time directly through 
pattern matching. Note that the cubical library has its own definition of contractibility, 
`isContr`.

```agda 
contr : isContr I 
contr = 𝒾₀ ,  f 
  where 
    -- Left as exercise
    f : (j : I) → 𝒾₀ ≡ j
    f 𝒾₀ = refl
    f 𝒾₁ = seg
    f (seg i) j = seg (i ∧ j) 
``` 

# Propositional truncation

# Set quotients (quotient types)

# The circle

