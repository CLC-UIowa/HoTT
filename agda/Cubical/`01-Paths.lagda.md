```agda 
module `01-Paths where 

open import Prelude.Base public 
``` 


# Cubical Agda 
We will be using the standard cubical agda library. 
  - https://github.com/agda/cubical
  - https://agda.readthedocs.io/en/latest/language/cubical.html
  - Cubical Agda: A dependently typed programming language with univalence and higher inductive types
    - https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cubical-agda-a-dependently-typed-programming-language-with-univalence-and-higher-inductive-types/839F14B5227969B039D7B57AA8272C6B

```agda 
open import Cubical.Foundations.Prelude 
  renaming (I to 𝕀 ; i0 to i₀ ; i1 to i₁)
  hiding 
    (module Σ ; 
     Σ-syntax ; 
     cong ; 
     sym ; 
     refl ; 
     funExt ; 
     transport ; 
     _∙_ ; 
     J ; 
     Path) public
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

# The interval type

In Cubical Agda, we have
- a type 𝕀, such that
- i₀ : 𝕀 
- i₁ : 𝕀 


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

for all t ∈ [0, 1]. Now, consider a path between paths in cubical type theory. Perhaps: 

```notAgda 
uip : {x y : A} → (p q : x ≡ y) → p ≡ q 
``` 
The paths p and q each have type 𝕀 → A, hence (p ≡ q) elaborates to:
```notAgda 
(p ≡ q) i : x ≡ y
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

# Cubical Type Theory

## The interval type

Cubical type theory introduces the interval type I with inhabitants
- i₀ : 𝕀
- i₁ : 𝕀
to model the real unit interval [0, 1]. A variable i : I corresponds
to a point in the interval [0, 1]---even if we may only canonically
observe it as either the endpoint i₀ or the endpoint i₁.

Elements of the interval form a De Morgan Algebra, with minimum ∧, maximum
∨, and negation ~. If it helps, you may remember these behaviors as 
the minimum ∧ being the meet (GLB) and maximum ∨ as the join (LUB).
Or, as the corresponding boolean operators.

```notAgda
_∧_ : 𝕀 → 𝕀 → 𝕀 
_∨_ : 𝕀 → 𝕀 → 𝕀 
~_ : 𝕀 → 𝕀 
``` 

Being a De Morgan Algebra means satisfying the following equations:

| i  | j  | i ∧ j  | i ∨ j   | ~ i | ~ j |
|----|----|--------|---------|-----|-----|
| i₀ | i₀ | i₀     | i₀      | i₁  | i₁  |
| i₀ | i₁ | i₀     | i₁      | i₁  | i₀  |
| i₁ | i₀ | i₀     | i₁      | i₀  | i₁  |
| i₁ | i₁ | i₁     | i₁      | i₀  | i₀  |

As a consequence, we observe the following De Morgan laws:
- Commutativity: i ∧ j = j ∧ i, and i ∨ j = j ∨ i 
- involution : ~ (~ i) = i 
- Distributivity (De Morgan's laws):
  - ~ (i ∨ j) = ~ i ∨ ~ j
  - ~ (i ∧ j) = ~ i ∨ ~ j 

Note that the interval type does not form a **Boolean algebra**:
the following formulae
- i ∧ ~ i = i₀ 
- i ∨ ~ i = i₁ 
are only true for i ∈ {i₀ , i₁}, and *not* valid for arbitrary i ∈ [0, 1]. For example,
it's not the case that that 0.5 ∨ 0.5 = 1. That is to say, interval variables 
model "arbitrary points" along the interval [0, 1], despite only being observable at the endpoints. 

## The Path type

Cubical TT introduces a primitive for **dependent** paths:

```notAgda
PathP : ∀ {ℓ} (A : 𝕀 → Set ℓ) → A i₀ → A i₁ → Set ℓ
```

Non-dependent paths are a degenerate case in which 
the type family is constant. 

```agda
Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A = PathP (λ _ → A) 
```

The major shift in thought is that this "Path" type is
what we take to be the identity, and hence (x ≡ y) is 
syntactic sugar for Path A x y.

Like a path in topology, inhabitants of the type PathP type are functions
out of the interval I. E.g., the type (x ≡ x) = PathP (const A) x x is 
effectively a type (I → A) subject to the condition that, an inhabitant
f : x ≡ x should have
- f i₀ = x 
- f i₁ = x 

In other words, f is a constant function returning x. 
We may define `refl` now as the "constant path".
```agda 
refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x 
refl {x = x} i = x 
```

**Remark.** Be careful not to *literally* equate the types (𝕀 → A)
and Path A x y (or, x ≡ y). The two are separate types that use the same term syntax.
That is, we can write:

```agda
notRefl : ∀ {ℓ} {A : Set ℓ} {x : A} → 𝕀 → A 
notRefl {x = x} i = x 
```

But we do not have that refl ≡ notRefl, as the two are at fundamentally
different types: refl is a path type, notRefl is a function type.
It just so happens that we use the same term syntax to inhabit both.

We use refl now to prove that Path A x y ≡ (x ≡ y)---indeed, the 
latter is syntactic sugar. 
 
```agda 
module _ where 
  open GVars 

  private variable
    x y z : A 
  _ : Path A x y ≡ (x ≡ y)
  _ = refl 
```

### Dependent paths: Book HoTT vs Cubical Agda 

Dependent paths describe paths between terms at different (but convertible!) types.
There are two alternatives in vanilla MLTT. One is heterogeneous equality, `_≅_`,
which permits the equation of terms at different (but convertible) types!

```agda 
  module _ where private 
    data _≅_ {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set (lsuc ℓ) where
      refl-≅ : x ≅ x
    
    ≅-to-type-≡ : ∀ {A B : Set ℓ} {x : A} {y : B} → x ≅ y → A ≡ B 
    ≅-to-type-≡ refl-≅ = refl  
```

Given `x : A` and `y : B`, The type `x ≅ y` is equivalent to the type 
`Σ[ pf ∈ A ≡ B] (coerce pf x ≡ y)`. That is, an inhabitant `p : x ≅ y` tells us 
precisely (and only) that
- the types of `x` and `y` are equal, and 
- the coercion of `x` to type `B` is equal to `y`. 

In fact we are fully capable of producing a dependent path from a 
heterogeneous equality: 
```agda 
    ≅-to-PathP : {A B : Set ℓ} {x : A} {y : B} → x ≅ y → Set ℓ 
    ≅-to-PathP {x = x} {y = y} e = PathP (λ i → (≅-to-type-≡ e) i) x y 
``` 

And for this reason we'll adopt the following syntax for dependent paths:

```agda 
  _≅[_]≅_ : {A B : Set ℓ} (x : A) (e : A ≡ B) (y : B) → Set ℓ 
  x ≅[ e ]≅ y = PathP (λ i → e i) x y 
```    

Unfortunately, heterogeneous equality only runs smoothly with the UIP, and so is
not terribly popular with HoTT folks. 

The HoTT folks instead will often write, e.g. in Book HoTT, the expression 

```notAgda 
u =^{P}_{e} v
``` 


to denote the **dependent path** type `tr P e u ≡ v`, given 
- x, y : A 
- P : A → Set 
- u : P x 
- v : P y
- e : x ≡ y. 

In other words, we assert that `u` and `v` are equal provided `u` is 
coerced to the type of `v`.

The type `PathP` is precisely this idea, but codified into the object language.
That is, `PathP (P ∘ e) u v` is a dependent path from `u : P x` to `v : P y`. 
Again, the idea is that `e : x ≡ y` implies that `P x ≡ P y`, so 
(thinking heterogeneously) it is sensible to equate `u : P x` and `v : P y`.

## An equivalence relation, and other properties

### Symmetry 

Like with an inductively defined `_≡_`, 
we must derive other expected properties of equality.

Symmetry follows from negation of the interval variable. Observe
that 
- p : x ≡ y, or p : 𝕀 → A
- p i₀ = x
- p i₁ = y

And so p (~ i) equates to:
- p (~ i₀) = p i₁ = y
- p (~ i₁) = p i₀ = x 
and hence p (~ i) : 𝕀 → A can be assigned type y ≡ x.

```agda
  _⁻¹ : x ≡ y → y ≡ x
  (p ⁻¹) i =  p (~ i) -- i = p (~ i) 
```

Because equalities behave like functions, certain identities now compute definitionally.

For example, refl is its own inverse:

refl = λ i → x 
refl ⁻¹ i = (λ i → x) (~ i)
          = x 
refl ⁻¹   = λ i → x  
          = refl
```agda 
  refl⁻¹ : refl ⁻¹ ≡ refl {x = x}
  refl⁻¹ = refl 
```

And that symmetry is an involution:

```agda 
  sym-involutive : ∀ (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p 
  sym-involutive p = refl 
```

### The action on paths

The action on paths is definable simply as the composition of f : A → B and p : x ≡ y.
Observe that
- p i₀ ≡ x 
- p i₁ ≡ y

and so f (p i) computes as follows:
- f (p i₀) ≡ f x 
- f (p i₁) ≡ f y

Hence f (p i) : f x ≡ f y.

Of course, f : A → B is a function type and p : x ≡ y is a path type,
so the application f ∘ p is ill-typed. Hence I'll define a separate 
operator _·_ (\cdot) to denote the composition of f and p. That is, intuitively
(but not literally), 
- p : 𝕀 → A (as path type), and  
- f : A → B (as function type), 
so f · p : 𝕀 → B, albeit that of course that f · p : f x ≡ f y.

```agda
  infixr 5 _·_
  ap _·_ : (f : A → B) → x ≡ y → f x ≡ f y 
  ap f p i = f (p i) 

  -- \cdot 
  _·_ f = ap f 
```

On the other side, sometimes we wish to compose a function with 
a path to yield a function type. For example, given type family P : A → Set ℓ 
and  e : x ≡ y at type A, we might wish to yield a function P ∘ e : 𝕀 → Set ℓ.
Because I am a psychopath, I will use an identical looking but technically
separate unicode character ∙ (which is `\.`) to denote:

```agda 
  -- \. 
  infixr 5 _∙_
  _∙_ : {x y : A} (P : A → Set ℓ) → x ≡ y → (𝕀 → Set ℓ) 
  (P ∙ e) i = P (e i) 
``` 

Functorial properties of the action on paths now compute definitionally.
For example, for p : x ≡ y, 
  (id · p) i
= id (p i)
= p i

```agda 
  ap-id : (p : x ≡ y) → id · p ≡ p 
  ap-id p = refl 
```

Composition likewise computes definitionally. Given f : A → B, G : B → C, and p : x ≡ y,
  ((g ∘ f) · p) i
= g (f (p i))
= g ((f · p) i)
= (g · (f · p)) i

```
  ap-comp : (f : A → B) (g : B → C) (p : x ≡ y) → (g ∘ f) · p ≡ g · (f · p)
  ap-comp f g p = refl 
``` 

### Transitivity 

Defining transitivity dives deeper into the crevices of cubical TT than I'd
like to go. For now, we may assume an operator
```notAgda
_∙∙_∙∙_ : (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → x ≡ w
```

where (p ∙∙ q ∙∙ r) can be thought of as "filling" the top line 
of the following square:

```notAgda

       x ∙ ∙ ∙ > w
       ^         ^
   p⁻¹ |         | r        ^
       |         |        j |
       y — — — > z          ∙ — >
            q                 i
```

Hence the cube induced by (refl ∙∙ q ∙∙ r), for q : x ≡ y and r : y ≡ z, is:

```notAgda
      x ∙ ∙ ∙ > z
      ^         ^
 refl |         | r        ^
      |         |        j |
      x — — — > y          ∙ — >
            q                 i

```

That is, transitivity is the missing face of this cube.

```agda 
  _○_ : x ≡ y → y ≡ z → x ≡ z 
  (p ○ q) = refl ∙∙ p ∙∙ q
```

## Function extensionality

Function extensionality is entirely straightforward to define on path types.
Define a homotopy accordingly:

```
_∼_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} (f g : (x : A) → B x) → Set _
_∼_ {A = A} f g = (x : A) → f x ≡ g x
```

The type f ≡ g can be understood 
as the type 𝕀 → (A → B), and hence fun-ext H i : (x : A) → B x,
subject to the condition that 
- fun-ext H i₀ = f 
- fun-ext H i₁ = g.

This gives us an x : A to work with. It follows that
- H x i₀ = f x 
- H x i₁ = g x 
hence H x i : f x ≡ g x. Specifically, we have
- fun-ext H i₀ x = H x i₀ = f x 
- fun-ext H i₁ x = H x i₁ = g x
and so un-applying the variable x yields
- fun-ext H i₀ = λ x → f x = f
- fun-ext H i₁ = λ x → g x = g 
as desired.

```agda
fun-ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} → 
          f ∼ g → f ≡ g 
fun-ext {f = f} {g} H i x = H x i
```


## The transport primitive

Whereas vanilla MLTT defines J as the primitive operator
on equality types, cubical type theory takes transport as primitive.
(It is effectively folklore that either can be presumed as primitive to derive the other.)

The generalized transport is for families indexed by the the interval 𝕀. We will
show that from it we can recover the usual `tr : (P : A → 𝒰) → x ≡ y → P x → P y`.


```notAgda 
transp : ∀ {ℓ} (A : 𝕀 → Set ℓ) (r : 𝕀) → A i₀ → A i₁ 
``` 

That is, given an I-index type family A, we may transport 
from A i₀ to A i₁.

It is a sensible question why we include the argument (r : 𝕀). The answer 
dives deeper into the alcoves of cubical Agda than I'd like to take us. 
We will ignore it for now and likely the remainder of this tutorial.

## Notation 

Let us introduce some notation for transports. In Rijke and HoTT, 
the term `tr` describes the transport of a term `a : P x` to type `P y`,
which we can recover from the generalized transport `transp`.

The insight here is that composition of P : A → Set ℓ with 
e : x ≡ y yields a type family (P ∙ e) : 𝕀 → Set ℓ. Accordingly,
we should observe that 
- (P ∙ e) i₀ = P x, and 
- (P ∙ e) i₁ = P y. 

```agda
module _ where
  open GVars
  private variable
    x y : A 

  tr : (P : A → Set ℓ) → x ≡ y → P x → P y 
  tr P e = transp (P ∙ e) i₀
``` 

As described above, PathP is used to described a "dependent path", which is 
otherwise defined in Book Hott as the type `tr P e u ≡ v` to describe 
a dependent path from `u : P x` to `v : P y`. As such, we should expect
to be able to translate from the Book HoTT notion to the cubical notion.
This behavior is defined in the Cubical library as `toPathP`:

```agda    
  _ : ∀ {P : A → Set ℓ} (e : x ≡ y) (u : P x) (v : P y) → 
                  tr P e u ≡ v → 
                  PathP (λ i → P (e i)) u v
  _ = λ e u v d →  toPathP d
```

The Cubical library reserves the term `transport` for When the type family `P` 
is the identity. I often call this term "coerce", but this is not quite accurate---
when the equality `e : A ≡ B` is introduced via univalence, it is not the case that 
we are simply casting a term from type A to B. Rather, transporting along that path may change 
the value of x : A. For example, `coerce Not true ≡ false`, given `Not : Bool ≡ Bool` is the
automorphism introduced by univalence on the `not : Bool → Bool`. equivalence.

```agda  
  transport : A ≡ B → A → B 
  transport = tr id  
``` 

We introduce the syntactic sugar `p ▸ x` for transporting `x` along path `p`. 

```agda 
  _▸_ : A ≡ B → A → B 
  p ▸ x = transport p x
``` 


As stated earlier, it is well known that transport
is sufficient to derive an induction principle J.

```agda
  J : (x : A) (P : ∀ y → x ≡ y → Set ℓ)  → 
      P x refl → (y : A) → (p : x ≡ y) → 
      P y p 
```

Our definition will use interval variables in a creative fashion. 
We will simply show, given d : P x refl, that we can transport d to type P y p
given an appropriate path e : P x refl ≡ P y p. 

```notAgda
J x p d y p = e ▸ d
```

Given y : A and p : x ≡ y, We must produce a path 
e : P x refl ≡ P y p such that
- e i₀ = P x refl 
- e i₁ = P y p

Note that 
- P (p i₀) = P x 
- P (p i₁) = P y
And so P (p i) = P x ≡ P y. 

P next expects an argument of type x ≡ (p i), hence
we must supply a path G : x ≡ p i such that
- P (p i₀) (G i₀) = P x refl 
- P (p i₁) (G i₁) = P y p
That is, we should have
- G i₀ = refl
- G i₁ = p 

Which implies that we have
- G i₀ j = x 
- G i₁ i₀ = x 
- G i₁ i₁ = y 

In other words, G i j should equal x *except* 
when both i and j are i₁. This is precisely
the behavior of p (i ∧ j), as 
- p i₀ = x
- p i₁ = y 
and p (i ∧ j) = y iff i = i₁ = j.

```agda
  J x P d y p = e ▸ d
    where
      G : (i : 𝕀) → x ≡ p i     
      G i j = p (i ∧ j)  
         
      e : P x refl ≡ P y p
      e i = P (p i) (G i)
```

# In summary

- Propositional equalities are now paths; 
- The path x ≡ y behaves as a function out of the interval f : 𝕀 → A
  subject to 
    - f i₀ = x 
    - f i₁ = y; 
- The usual properties of equality hold;
- We may also describe paths from terms `u : P x`, `v : P y` with 
  convertible types: `PathP (λ i → P (e i)) u v`; and  
- the transport operator `transp` is now primitive.
