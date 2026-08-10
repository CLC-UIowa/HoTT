```agda 
module Prelude.Paths where 

open import Prelude.Base public 
open GVars 
``` 


# Cubical Agda 
We will be using the standard cubical agda library. 
  - https://github.com/agda/cubical
  - https://agda.readthedocs.io/en/latest/language/cubical.html

```agda 
open import Cubical.Foundations.Prelude hiding (module Σ ; Σ-syntax) public
``` 

Here are some other resources and papers on cubical type theory.
- 1lab (paths and transport):
  - https://amelia.how/posts/cubical-type-theory.html
  - https://1lab.dev/1Lab.Path.html
- Cyril Cohen, Thierry Coquand, Simon Huber, and Andres Mörtberg. 
  Cubical Type Theory: a constructive interpretation of the univalence axiom.
  - https://arxiv.org/pdf/1611.02108 
- Thierry Coquand, Simon Huber, Anders Mörtberg. On Higher Inductive Types in Cubical Type Theory.
  - https://arxiv.org/abs/1802.01170


# The path type

A path (x ≡ y) in cubical type theory is *not* the standard MLTT identity type. 
Rather, for x , y : A, it is a type

```notAgda 
  (x ≡ y) = (i : 𝕀) → A 
``` 

such that, given p : x ≡ y, we have 
- p i₀ = x 
- p i₁ = y 

## Paths in topology 

We will draw intuition from standard topology, as per 
[wikipedia](https://en.wikipedia.org/wiki/Path_(topology)). 

In topology, a **path** from x₀ to x₁ is a continuous function 
f : [0 , 1] → X, such that 
- f(0) = x₀ 
- f(1) = x₁ 

A **homotopy** is defined as a continuous function 
H : X × [0, 1] → Y such that 
- H(x , 0) = f(x)
- H(x, 1)  = g(x) 

If we curry the definition to H : X → (𝕀 → Y), 
we see that H accepts an input x ∈ X and returns a *path*. 

Now hopefully it is clear why we define a homotopy between f, g : A → B, in type theory, as 

```notAgda 
f ∼ g : (x : A) → f x ≡ g x 
``` 
The type (f x ≡ g x), in cubical Agda, is a path type, 
meaning it's (in actuality) a function with type 𝕀 → B. Hence 

```notAgda 
f ∼ g : (x : A) → (𝕀 → B)
``` 

So a homotopy accepts an input x ∈ A and returns a **path** from f(x) to g(x)! 
Because H x : (f x ≡ g x) is a **path**, it's subject to the condition for all x ∈ A that:
- H(x , i₀) = f x 
- H(x , i₁) = g x 

In other words, H is precisely the analogue of a topological homotopy. Compare:
- In topology, we have H : X × [0 , 1] → Y s.t. 
  - H(x, 0) = f(x)
  - H(x, 1) = g(x)
- In Cubical Type Theory, we have H : A → (𝕀 → B) s.t. 
  - H x i₀ = f x
  - H x i₁ = g x 

## Path homotopies 

When we equate two paths, we end up with a path homotopy.
In topology, a **homotopy of paths** in X is a family of paths 
f : [0, 1] → [0, 1] → X such that 
- f t 0 = x₀ 
- f t 1 = x₁ 

for all x ∈ X. Now, consider a path between paths in cubical type theory. Perhaps: 

```notAgda 
uip : {x y : A} → (p q : x ≡ y) → p ≡ q 
``` 
The paths p and q each have type 𝕀 → A, hence (p ≡ q) elaborates to:
```notAgda 
(p ≡ q) = 𝕀 → (𝕀 → A)
``` 
A given path homotopy H : p ≡ q is subject to the condition that:
for all i ∈ 𝕀, we have: 
- H i i₀ = x 
- H i i₁ = y 

and, for all j ∈ 𝕀, we have: 
- H i₀ j = p j
- H i₁ j = q j

Or, specifically,

| i  | j | H i j |
| -- | -- | ---- |
| i₀ | i₀ | x    |
| i₁ | i₀ | x    | 
| i₀ | i₁ | y    | 
| i₁ | i₁ | y    | 

So to prove p ≡ q we must find such a function H. (No such function exists, of course,
for this specific example.)

## The computational behavior of paths & transport
The following resources help us understand transports.

  - https://amelia.how/posts/cubical-type-theory.html
  - https://1lab.dev/1Lab.Path.html


-- transp is a generalized transport for dependent
-- paths, primitive to cubical Agda. It has the following type.
--   transp : {ℓ : I → Level} → (A : (i : I) → Type (ℓ i)) → I → A i0 → A i1

-- transp (λ _ → A) i1 x definitionally equals x
transpi1 : ∀ (x : A) → transp (λ _ → A) i1 x ≡ x 
transpi1 x = refl 

-- transp (λ _ → A) i0 x propositionally equals x
transpi0 : ∀ (x : A) → transp (λ _ → A) i0 x ≡ x 
transpi0 {A} x i = transp (λ i → A) i x

-- combining the two
transpEq : ∀ (x : A) (i : I) → transp (λ _ → A) i x ≡ x 
transpEq {A = A} x i j = transp (λ _ → A) (j ∨ i) x 


# Definitions and notation from Rijke 

Some definitions we have grown accustomed to are not in the Cubical library,
and so will have to be redefined with respect to path equality.

## AP and transport 
We rename "cong" to "ap", and add some other friendly names.

```agda 
module _ where 
  private
    variable
      x y z w : A

  ap : (f : A → B) → x ≡ y → f x ≡ f y 
  ap = cong 

  tr : (P : A → Set ℓ) → x ≡ y → P x → P y
  tr P e = transp (λ i → P (e i)) i0 
  
  -- Star notation for mapping 
  _* : (f : A → B) → x ≡ y → f x ≡ f y
  f * = ap f 

  -- transports 
  -- syntactic sugar for transports (\tb2)
  infixr 5 _▸_ 
  _▸_ : ∀ {P : A → Set ℓ} → x ≡ y → P x → P y
  p ▸ x = tr _ p x 

  -- With explicit motive 
  infixr 5 _⟨_⟩▸_
  _⟨_⟩▸_ :  ∀ (P : A → Set ℓ) → x ≡ y → P x → P y
  _⟨_⟩▸_ = tr
``` 

## Homotopioes 

```agda 
module _ where 
  open GVars 
  infix 4 _∼_
  
  _∼_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → ((x : A) → B x) → ((x : A) → B x) → Set _
  _∼_ {A = A} f g = (x : A) → f x ≡ g x
``` 
