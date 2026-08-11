```agda
module Univalence where

open import Prelude.Paths hiding (or ; tr ; coerce ; _▸_ ; transport ; _*_)
open GVars 
```

# Univalence 

Finally, we are going to demonstrate the **computational content** of univalence 
in cubical Agda. Namely, we will witness that transporting along a univalent path 
in fact reduces according to the equivalence.

## Notation 

Let us introduce some notation for transports. In Rijke and HoTT, 
the term `tr` describes the transport of a term `a : P x` to type `P y`: 

```agda 
tr : (P : A → Set ℓ) → {x y : A} → x ≡ y → P x → P y 
tr P e = transp (λ i → P (e i)) i0
``` 

The Cubical library reserves the term `transport` for When the type family `P` is constant.
I often call this term "coerce", but this is not quite accurate---when the equality 
`e : A ≡ B` is introduced via univalence, it is not the case that we are simply 
casting a term from type A to B. Rather, transporting along that path may change 
the value of x : A. 

```agda  
coerce transport : A ≡ B → A → B 
transport = tr _ 
coerce = transport 
``` 

We introduce the syntactic sugar `p ▸ x` for transporting `x` along path `p`. 

```agda 
_▸_ : A ≡ B → A → B 
p ▸ x = transport p x
``` 

## Computational univalence with Booleans 

Let's first witness the two identities of Bool. 

```agda 

Id Not : Bool ≡ Bool 
Id = refl 

not-involution : ∀ b → not (not b) ≡ b 
not-involution true = refl 
not-involution false = refl 


Not = (ua ∘ isoToEquiv) (iso not not not-involution not-involution)
``` 

Now transporting along `Not` definitionally negates the term:  

```agda
_ :   Not ▸ true ≡ false
    × Not ▸ false ≡ true 
_ = refl , refl 
``` 

This is the basest of expectation we can have of computational univalence:
that `transport (ua e) x ≡ e .fst x` for `e : A ≃ B`. 

More interesting is to transport functions and proofs along univalence.
For example, we can transport `and : Bool → Bool → Bool` along the family 
Not-Fam

```agda
Not-Fam : (Bool → Bool → Bool) ≡ (Bool → Bool → Bool)
Not-Fam i = Not i → Not i → Not i
```  

to get the negated function `or x y = ¬ (¬ x ∧ ¬ y)`, which, by by De Morgan algebra laws, entails:

```notAgda 
  or x y 
= ¬ (¬ x ∧ ¬ y)
= ¬ (¬ (x ∨ y))
= x ∨ y
``` 


```agda
or : Bool → Bool → Bool
or = Not-Fam ▸ and
``` 

Most interesting is, it is not simply that we may show by induction that 
`or` is pointwise equal to `λ x y → not (and (not x) (not y))`:

```agda 
or-table : ∀ (x y : Bool) → or x y ≡ not (and (not x) (not y))
or-table false false = refl
or-table false true  = refl 
or-table true false  = refl
or-table true true   = refl
``` 

But rather it is the case that `or` definitionally computes 
to `λ x y → not (and (not x) (not y))`: 

```agda 
or≡¬[¬x∧¬y] : or ≡ (λ x y → not (and (not x) (not y)))
or≡¬[¬x∧¬y] = refl 
``` 

The fuckery has just begun. We can choose to only transport the
last argument of `and` along the `Not` identification, to get `nand`.

```agda 
Nand-Fam : (Bool → Bool → Bool) ≡ (Bool → Bool → Bool)
Nand-Fam i = Id i → Id i → Not i 

nand : Bool → Bool → Bool
nand = Nand-Fam ▸ and
``` 

Again, we have that `nand` is definitionally equal to `not (and x y)`.
``` 
nand≡not-and : nand ≡ λ x y → not (and x y) 
nand≡not-and = refl 
``` 

Because of which, it is easy to lift proofs from `and` to `nand`, simply by congruence.

```agda
and-comm : ∀ (x y : Bool) → and x y ≡ and y x 
and-comm false false = refl
and-comm false true = refl
and-comm true false = refl
and-comm true true = refl 

nand-comm : ∀ (x y : Bool) → nand x y ≡ nand y x 
nand-comm x y = ap not (and-comm x y) 

``` 

More interesting is to transport a proof of `and` commutativity to `or` commutativity. 
We first show that there is a (dependent) path from `and` to `or` along the 
family `Not-Fam i = Not i → Not i → Not i`.

```agda
and→or : PathP (λ i → Not i → Not i → Not i) and or 
and→or i = transp {ℓ = λ _ → lzero} (λ j → Not (i ∧ j) → Not (i ∧ j) → Not (i ∧ j)) (~ i) and 
``` 

Because this is a path from `and` to `or`, we have that `and→or i0 = and` and `and→or i1 = or`:

```agda 
_ :   (and→or i0 ≡ and)
    × (and→or i1 ≡ or) 
_ = refl , refl 
``` 

We use this to translate `and-comm` from a theorem concerning `and` to a theorem concerning `or`. 
That is, we transport it from the type `(x y : Bool) → and x y ≡ and y x` to the type 
`(x y : Bool) → or x y ≡ or y x`. Cubically, we must simply produce a path 
that has the former type at i0 and the latter type at i1; the dependent path 
`and→or` computes as such, yielding:

```agda
G : ((x y : Bool) → and x y ≡ and y x) ≡ ((x y : Bool) → or x y ≡ or y x) 
G i = (x y : Not i) → and→or i x y ≡ and→or i y x
```

The interval variable `i` serves as a switch for `and→or`, and so:

```agda  
_ :   (G i0 ≡ ∀ (x y : Bool) → and x y ≡ and y x)
    × (G i1 ≡ ∀ (x y : Bool) → or x y ≡ or y x)
_ = refl , refl 
``` 

Hence we may transport the proof `and-comm` along path `G` to get a 
proof that `or` is commutative.

```agda 
or-comm : ∀ (x y : Bool) → or x y ≡ or y x 
or-comm =  G ▸ and-comm 
``` 


# Works Cited 
- Andrea Vezzosi, Anders Mörtberg, Andreas Abel. Cubical Agda: A dependently typed programming language with univalence and higher inductive types. 
  - https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cubical-agda-a-dependently-typed-programming-language-with-univalence-and-higher-inductive-types/839F14B5227969B039D7B57AA8272C6B
