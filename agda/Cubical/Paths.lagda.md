```agda 
module Paths where 

open import Prelude.Base public 
``` 


# Cubical Agda 
We will be using the standard cubical agda library. 
  - https://github.com/agda/cubical
  - https://agda.readthedocs.io/en/latest/language/cubical.html
  - Cubical Agda: A dependently typed programming language with univalence and higher inductive types
    - https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cubical-agda-a-dependently-typed-programming-language-with-univalence-and-higher-inductive-types/839F14B5227969B039D7B57AA8272C6B

```agda 
open import Cubical.Foundations.Prelude hiding (module Σ ; Σ-syntax ; cong ; sym ; refl ; funExt ; J) public
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

# Cubical Type Theory

## The interval type

Cubical type theory introduces the interval type I with inhabitants
- i0 : I
- i1 : I 
to model the real unit interval [0, 1]. A variable i : I corresponds
to a point in the interval [0, 1]---even if we may only canonically
observe it as either the endpoint i0 or the endpoint i1.

Elements of the interval form a De Morgan Algebra, with minimum ∧, maximum
∨, and negation ~. If it helps, you may remember these behaviors as 
the minimum ∧ being the meet (GLB) and maximum ∨ as the join (LUB).
Or, as the corresponding boolean operators.

```notAgda
_∧_ : I → I → I 
_∨_ : I → I → I 
~_ : I → I 
``` 

Being a De Morgan Algebra means satisfying the following equations:

| i  | j  | i ∧ j  | i ∨ j   | ~ i | ~ j |
|----|----|--------|---------|-----|-----|
| i0 | i0 | i0     | i0      | i1  | i1  |
| i0 | i1 | i0     | i1      | i1  | i0  |
| i1 | i0 | i0     | i1      | i0  | i1  |
| i1 | i1 | i1     | i1      | i0  | i0  |

As a consequence, we observe the following De Morgan laws:
- Commutativity: i ∧ j = j ∧ i, and i ∨ j = j ∨ i 
- involution : ~ (~ i) = i 
- Distributivity (De Morgan's laws):
  - ~ (i ∨ j) = ~ i ∨ ~ j
  - ~ (i ∧ j) = ~ i ∨ ~ j 

Note that the interval type does not form a **Boolean algebra**:
the following formulae
- i ∧ ~ i = i0 
- i ∨ ~ i = i1 
are only true for i ∈ {i0 , i1}, and *not* valid for arbitrary i ∈ [0, 1]. For example,
it's not the case that that 0.5 ∨ 0.7 = 1. That is to say, interval variables 
model "arbitrary points" along the interval [0, 1], despite only being observable at the endpoints. 

## The Path type

Cubical TT introduces a primitive for **dependent** paths:

```notAgda
PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
```

Non-dependent paths are a degenerate case.

```agda
Path′ : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path′ A x y = PathP (λ _ → A) x y 
```

The Cubical library already defines such a "Path" type, hence
we have written `Path′`. The major shift in thought is that this "Path" type is
what we take to be the identity, and hence (x ≡ y) is 
syntactic sugar for Path A x y.

Like a path in topology, inhabitants of the type PathP type are functions
out of the interval I. E.g., the type (x ≡ x) = PathP (const A) x x is 
effectively a type (I → A) subject to the condition that, an inhabitant
f : x ≡ x should have
- f i0 = x 
- f i1 = x 

In other words, f is a constant function returning x. 
We may define `refl` now as the "constant path".
```agda 
refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x 
refl {x = x} i = x 
```

**Remark.** Be careful not to *literally* equate the types (I → A)
and Path A x y. The two are separate types that use the same term syntax.
That is, we can write:

```agda
notRefl : ∀ {ℓ} {A : Set ℓ} {x : A} → I → A 
notRefl {x = x} i = x 
```

But we do not have that refl ≡ notRefl, as the two are at fundamentally
different types: refl is a path type, notRefl is a function type.
It just so happens that we use the same term syntax to inhabit both.


We use refl now to prove that Path′ A x y ≡ Path A x y ≡ (x ≡ y).
 
```agda 
module _ where 
  open GVars 

  private variable
    x y z : A 
  _ : Path′ A x y ≡ Path A x y
  _ = refl 

  _ : Path A x y ≡ (x ≡ y)
  _ = refl 
```

## An equivalence relation, and other properties

### Symmetry 

Like with an inductively defined `_≡_`, 
we must derive other expected properties of equality.

Symmetry follows from negation of the interval variable. Observe
that 
- p : Path A x y, or p : I → A
- p i0 = x
- p i1 = y

And so p (~ i) equates to:
- p (~ i0) = p i1 = y
- p (~ i1) = p i0 = x 
and hence p (~ i) : I → A can be assigned type y ≡ x.

```agda
  _⁻¹ : x ≡ y → y ≡ x
  (p ⁻¹) i = p (~ i) 
```

Because equalities are functions, certain identities now compute definitionally.

For example, refl is its own inverse:

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
- p i0 ≡ x 
- p i₁ ≡ y

and so f (p i) computes as follows:
- f (p i₀) ≡ f x 
- f (p i₁) ≡ f y

Hence f (p i) : f x ≡ f y.

Of course, f : A → B is a function type and p : x ≡ y is a path type,
so the application f ∘ p is ill-typed. Hence I'll define a separate 
operator _*_ to denote the composition of f and p.

```agda
  infixr 5 _*_
  ap _*_ : (f : A → B) → x ≡ y → f x ≡ f y 
  ap f p i = f (p i) 

  _*_ f = ap f 
```

Functorial properties of the action on paths now compute definitionally.
For example, for p : x ≡ y, 
  (id * p) i
= id (p i)
= p i

```agda 
  ap-id : (p : x ≡ y) → id * p ≡ p 
  ap-id p = refl 
```

Composition likewise computes definitionally. Given f : A → B, G : B → C, and p : x ≡ y,
  ((g ∘ f) * p) i
= g (f (p i))
= g ((f * p) i)
= (g * (f * p)) i

```
  ap-cong : (f : A → B) (g : B → C) (p : x ≡ y) → (g ∘ f) * p ≡ g * (f * p)
  ap-cong f g p = refl 
``` 

### Transitivity 

Defining transitivity dives deeper into the crevices of cubical TT than I'd
like to go. For now, we may assume an operator
```notAgda
_∙∙_∙∙_ : x ≡ y → y ≡ z → z ≡ w → x ≡ w
```

where (p ∙∙ q ∙∙ r) can be thought of as "filling" the top line 
of the following cube:

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
as the type I → (A → B), and hence fun-ext H i : (x : A) → B x,
subject to the condition that 
- fun-ext H i0 = f 
- fun-ext H i1 = g.

This gives us an x : A to work with. It follows that
- H x i0 = f x 
- H x i1 = g x 
hence H x i : f x ≡ g x. Specifically, we have
- fun-ext H i0 x = H x i0 = f x 
- fun-ext H i1 x = H x i1 = g x
and so un-applying the variable x yields
- fun-ext H i0 = λ x → f x = f
- fun-ext H i₁ = λ x → g x = g 
as desired.

```
fun-ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x} → 
          f ∼ g → f ≡ g 
fun-ext {f = f} {g} H i x = H x i 
```


## The transport primitive

Whereas vanilla MLTT defines J as the primitive operator
on equality types, cubical type theory takes transport as primitive.
(It is effectively folklore that either can be presumed as primitive to derive the other.)

The generalized transport is for families indexed by the the interval I. We will
show that from it we can recover the usual `tr : (P : A → 𝒰) → x ≡ y → P x → P y`.


```agda 
transp′ : ∀ {ℓ} (A : I → Set ℓ) (r : I) → A i0 → A i1
transp′ A r a = {!transp A r a!} -- transp A r a 

``` 

It is a sensible question why we include the argument (r : I). My frank opinion
is that this is (among many other places) where cubical TT begins to feel ad-hoc.


The documentation writes 

> The transport operation is generalized in the sense that it lets us specify where it is 
> the identity function.
> ...
> There is an additional side condition to be satisfied for a usage of transp to type-check:
> A should be a constant function whenever the constraint r = i1 is satisfied. By constant 
> here we mean that A is definitionally equal to λ _ → A i0, which in turn requires 
> A i0 and A i1 to be definitionally equal as well.

We have that transp computes as the identity when r = i1.

```
module _ {ℓ} (A : I → Set ℓ) (a : A i0) where
  
  _ : transp (λ _ → A i0) i1 a ≡ a 
  _ = refl 
```

which, the authors write,

> is only sound if in such a case A is a trivial path, as the side condition requires.

I won't discuss this technicality further.

We can recover the usual definition of transport using `transp`.

```agda
module _ where
  open GVars
  private variable
    x y : A 

  tr : (P : A → Set ℓ) → x ≡ y → P x → P y 
  tr P e = transp (λ i → P (e i)) i0   
``` 

The Cubical library uses the term `transport` for when P is a constant family.
I like the following in-fix notation. 

```   
  -- syntactic sugar for transports (\tb2)
  infixr 5 _▸_ 
  _▸_ : A ≡ B → A → B
  p ▸ x = transport p x

  -- Transport with explicit motive 
  infixr 5 _⟨_⟩▸_
  _⟨_⟩▸_ :  ∀ (P : A → Set ℓ) → x ≡ y → P x → P y
  _⟨_⟩▸_ = tr
```

As stated earlier, it is well known that transport
is sufficient to derive an induction principle J.

```agda
  J : (x : A) (P : ∀ y → x ≡ y → Set ℓ)  → 
      P x refl → (y : A) → (p : x ≡ y) → 
      P y p 
```

Our definition more specifically uses interval variables in a creative fashion. 
We will simply show, given d : P x refl, that we can transport d to type P y p.

```no
J x p d y p = e ▸ d
```

Given y : A and p : x ≡ y, We must produce a path 
e : P x refl ≡ P y p such that
- e i0 = P x refl 
- e i1 = P y p

Note that 
- P (p i0) = P x 
- P (p i1) = P y
And so P (p i) = P x ≡ P y. 

P next expects an argument of type x ≡ (p i), hence
we must supply a path G : x ≡ p i such that
- P (p i0) (G i0) = P x refl 
- P (p i1) (G i1) = P y p
That is, we should have
- G i0 = refl
- G i1 = p 

Which implies that we have
- G i0 j = x 
- G i1 i0 = x 
- G i1 i1 = y 

In other words, G i j should equal x *except* 
when both i and j are i1. This is precisely
the behavior of p (i ∧ j), as 
- p i0 = x
- p i1 = y 
and p (i ∧ j) = y iff i = i1 = j.

```agda
  J x P d y p = e ▸ d
    where
      G : (i : I) → x ≡ p i     
      G i j = p (i ∧ j)   
         
      e : P x refl ≡ P y p
      e i = P (p i) (G i) 
```

This is as far as I am going to take us today.

