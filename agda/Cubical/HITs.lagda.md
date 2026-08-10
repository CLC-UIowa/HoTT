```agda
module HITs where

open import Prelude.Paths
```

# The interval as a HIT

In ./Postulate.lagda.md, we explored the interval type as a postulated higher inductive type.
Now, for the first time, we will explore it as a HIT in *cubical Agda*, which allows a direct
definition. Note that the cubical library / flag permit the definition of **path constructors**
directly on 𝕀!


```agda 
data 𝕀 : Set where 
    i₀ : 𝕀 
    i₁ : 𝕀
    seg : i₀ ≡ i₁ 
``` 

## The recursion/induction principle

Let's first observe that pattern matching on 𝕀 produces the desired recursion and
induction principles, and that these compute definitionally.

```agda
𝕀-ind : ∀ {ℓ} (P : 𝕀 → Set ℓ) (x : P i₀) (y : P i₁) → 
          (p : PathP (λ i → P (seg i)) x y) → ((i : 𝕀) → P i)
𝕀-ind P x y p i₀ = x
𝕀-ind P x y p i₁ = y
```
Critically, we have that pattern matching on i : 𝕀 also produces
an obligation to produce a term M at type P (seg j) for j : I subject
to the boundary conditions:
- M = x when j = i0 
- M = y when j = i1 

Let's first remark upon the insight this gives us regarding the
"general form" of elimination of a path constructor in cubical
type theory. Recall that the goal, when defining 
- f = 𝕀-ind P x y p : ((i : 𝕀) → P i)
is to map f over the arrow seg : i₀ ≡ i₁ to an arrow 
ap f seg : f i₀ ≡ f i₁. Of course, f i₀ : P i₀ and 
f i₁ : P i₁ are at different types, and so we can't equate f i₀ and f i₁ with 
a homogeneous path. We instead have a *dependent* path:

```notAgda
ap f seg : PathP (ap P seg) (f i₀) (f i₁)
```

Further, f i₀ = x and f i₁ = y definitionally.
Hence we see that, a term M : (j : I) → P (seg j)
subject to the boundary conditions 
- M i0 = f i₀ = x 
- M i1 = f i₁ = y
is precisely the arrow of type ap f seg we are looking for.

In other words: when defining f by pattern matching over
a HIT, we are required to ensure that ap f e is well-defined
and well-typed for each path constructor e.

```
𝕀-ind P x y p (seg j) = p j  
```



## 𝕀 is contractible 

As an exercise, we can prove that 𝕀 is contractible, this time directly through 
pattern matching. Note that the cubical library has its own definition of contractibility, 
`isContr`.

```agda 
contr : isContr 𝕀 
contr = i₀ ,  f 
  where 
    -- Left as exercise
    f : (j : 𝕀) → i₀ ≡ j
    f i = {!!} 
``` 

# Propositional truncation

# Set quotients (quotient types)

# The circle

