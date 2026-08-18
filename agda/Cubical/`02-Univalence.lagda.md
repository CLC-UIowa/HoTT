```agda
module `02-Univalence where

open import Prelude.Paths hiding (or)
open GVars 
```

# Univalence 

Finally, we are going to demonstrate the **computational content** of univalence 
in cubical Agda. Namely, we will witness that transporting along a univalent path 
in fact reduces according to the equivalence.

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

Because this is a path from `and` to `or`, we have that `and→or i₀ = and` and `and→or i₁ = or`:

```agda 
_ :   (and→or i₀ ≡ and)
    × (and→or i₁ ≡ or) 
_ = refl , refl 
``` 

We use this to translate `and-comm` from a theorem concerning `and` to a theorem concerning `or`. 
That is, we transport it from the type `(x y : Bool) → and x y ≡ and y x` to the type 
`(x y : Bool) → or x y ≡ or y x`. Cubically, we must simply produce a path 
that has the former type at i₀ and the latter type at i₁; the dependent path 
`and→or` computes as such, yielding:

```agda
G : ((x y : Bool) → and x y ≡ and y x) ≡ ((x y : Bool) → or x y ≡ or y x) 
G i = (x y : Not i) → and→or i x y ≡ and→or i y x
```

The interval variable `i` serves as a switch for `and→or`, and so:

```agda  
_ :   (G i₀ ≡ ∀ (x y : Bool) → and x y ≡ and y x)
    × (G i₁ ≡ ∀ (x y : Bool) → or x y ≡ or y x)
_ = refl , refl 
``` 

Hence we may transport the proof `and-comm` along path `G` to get a 
proof that `or` is commutative.

```agda 
or-comm : ∀ (x y : Bool) → or x y ≡ or y x 
or-comm =  G ▸ and-comm 
``` 

## Univalence with Naturals 

More practical is to observe an equivalence between types of which one is more suited
for reasoning and the other more suited for performance or implementation. In particular,
the unary and binary representations of naturals are equivalent, however the former 
has a nicer inductive structure. Because the two are equivalent, we can define operations 
and prove properties over the former and transport to the latter. 

We define the binary representation in *little-endian format*, read left to right
with no trailing zeroes. That is, the number 6 is 011 (rather than 110).

```agda 
infixr 0 `_ 
infixr 1 `0_ 
infixr 1 `1_
data Pos : Set where 
  1∎ : Pos 
  `0_ : Pos → Pos 
  `1_ : Pos → Pos 

data Bin : Set where 
  0∎ : Bin 
  `_ : Pos → Bin 

Zero One Two Three Four Five Six : Bin 
Zero = 0∎ 
One = ` 1∎ 
Two = ` `0 1∎
Three = ` `1 1∎ 
Four = ` `0 `0 1∎
Five = ` `1 `0 1∎
Six  = ` `0 `1 1∎
``` 

### Disjoint constructors

We will need some lemmas below that state equalities such as e.g. 

```notAgda
0∎ ≡ ` 1∎
```

are absurd. Unlike with Vanilla Agda's propositional equality `_≡_`, we cannot 
simply pattern match on this absurd equation. In general, Cubical Agda does not 
presume constructors are disjoint.

In order to disprove the equality of disjoint constructors, we'll
use the following encode/decode technique. This is also referred to as a "No Confusion" proof.
The technique is entirely analogous to giving a decision procedure for equality on `Bin` and `Pos`. 

We first describe a relation on Bin and Pos---a "coding"---that is ⊤ when two constructors are 
equal and ⊥ otherwise. In other words, we map structurally equal terms to ⊤ and ⊥ otherwise.

```agda
BinCode : Bin → Bin → Set 
PosCode : Pos → Pos → Set
BinCode 0∎ 0∎ = ⊤
BinCode 0∎ (` x) = ⊥
BinCode (` x) 0∎ = ⊥
BinCode (` x) (` y) = PosCode x y 


PosCode 1∎ 1∎ = ⊤
PosCode 1∎ (`0 y) = ⊥
PosCode 1∎ (`1 y) = ⊥
PosCode (`0 x) 1∎ = ⊥
PosCode (`0 x) (`0 y) = PosCode x y
PosCode (`0 x) (`1 y) = ⊥
PosCode (`1 x) 1∎ = ⊥
PosCode (`1 x) (`0 y) = ⊥
PosCode (`1 x) (`1 y) = PosCode x y
```

For the purpose of using the J eliminator, we'll show that these
relations are reflexive. (Observe that the functions `encodeBin` and `encodePos`
require precisely proofs that `BinCode x x` and `PosCode x x`.)

```agda
BinRefl : ∀ x → BinCode x x
PosRefl : ∀ x → PosCode x x 

BinRefl 0∎ = tt
BinRefl (` x) = PosRefl x

PosRefl 1∎ = tt
PosRefl (`0 x) = PosRefl x
PosRefl (`1 x) = PosRefl x
```

We will now exhibit an equivalence between identity
types and their codes. The *encode* direction converts
paths to codes, and is easy to prove via based-path induction
J.

```agda
encodeBin : ∀ (x y : Bin) → x ≡ y → BinCode x y 
encodePos : ∀ (x y : Pos) → x ≡ y → PosCode x y 

encodeBin x y e = J (λ y _ → BinCode x y) (BinRefl x) e 
encodePos x y e = J (λ y _ → PosCode x y) (PosRefl x) e
```

The decoding---from codes to equalities---is tedious but more or 
less straightforward.

```agda
decodeBin : ∀ (x y : Bin) → BinCode x y → x ≡ y
decodePos : ∀ (x y : Pos) → PosCode x y → x ≡ y

decodeBin 0∎ 0∎ c = refl
decodeBin 0∎ (` x) ()
decodeBin (` x) 0∎ ()
decodeBin (` x) (` y) c = cong `_ (decodePos x y c)

decodePos 1∎ 1∎ c = refl
decodePos (`0 x) (`0 y) c = cong `0_ (decodePos x y c)
decodePos (`1 x) (`1 y) c = cong `1_ (decodePos x y c)
```

We now show that these types are equivalent. Again,
mostly tedious boilerplate.

```agda

decodeBinRefl : ∀ x → decodeBin x x (encodeBin x x refl) ≡ refl
decodePosRefl : ∀ x → decodePos x x (encodePos x x refl) ≡ refl

decodeBinRefl 0∎ = refl
decodeBinRefl (` x) i = cong `_ (decodePosRefl x i)
decodePosRefl 1∎ = refl
decodePosRefl (`0 x) i = cong `0_ (decodePosRefl x i)
decodePosRefl (`1 x) i = cong `1_ (decodePosRefl x i)

encodeDecodeBin : ∀ x y → retract (decodeBin x y) (encodeBin x y)
encodeDecodePos : ∀ x y → retract (decodePos x y) (encodePos x y)

encodeDecodeBin 0∎ 0∎ b = refl
encodeDecodeBin (` x) (` y) b = encodeDecodePos x y b 

encodeDecodePos 1∎ 1∎ b = refl
encodeDecodePos (`0 x) (`0 y) b = encodeDecodePos x y b
encodeDecodePos (`1 x) (`1 y) b = encodeDecodePos x y b

BinEqv : ∀ (x y : Bin) → BinCode x y ≃ (x ≡ y)
PosEqv : ∀ (x y : Pos) → PosCode x y ≃ (x ≡ y)
BinEqv x y = 
  isoToEquiv 
  (iso (decodeBin x y) (encodeBin x y) 
  (σ x y) 
  (encodeDecodeBin x y)) 
  where
    σ : ∀ (x y : Bin) → section (decodeBin x y) (encodeBin x y)
    σ x y b = J  (λ y e → decodeBin x y (encodeBin x y e) ≡ e) (decodeBinRefl x) b 

PosEqv x y = isoToEquiv 
  (iso 
    (decodePos x y) 
    (encodePos x y) 
    (σ x y  ) 
    (encodeDecodePos x y)) 
  where
    σ : ∀ (x y : Pos) → section (decodePos x y) (encodePos x y)
    σ x y b = J  (λ y e → decodePos x y (encodePos x y e) ≡ e) (decodePosRefl x) b 
```

Finally, given an equivalence, we can for example translate an equality
such as 
```notAgda
0∎ ≡ ` `0 p
```
to the type
```notAgda 
BinCode 0∎ (` `0 p) ≡ ⊥
```

hence exhibiting a proof that the constructors are disjoint.
For example, we have, by univalence, that the above identity holds:

```agda 
module _ (p : Pos) where 
  _ : (0∎ ≡ (` `0 p)) ≡ ⊥ 
  _ = ua (BinEqv 0∎ (` `0 p)) ⁻¹
``` 

which means we may transport by this equality to disprove it.

```agda 
  _ : ¬ (0∎ ≡ (` `0 p))
  _ = transport (ua (BinEqv 0∎ (` `0 p)) ⁻¹) 
``` 

### Plumbing 

Now we write conversions between the two representations:

```agda 
open import Data.Nat using (_*_ ; _+_)
-- Helper for incrementing a Pos
sucPos : Pos → Pos
sucPos 1∎     = `0 1∎
sucPos (`0 p) = `1 p
sucPos (`1 p) = `0 (sucPos p)

-- Helper for incrementing a Bin
sucBin : Bin → Bin
sucBin 0∎     = ` 1∎
sucBin (` p)  = ` (sucPos p)

ℕ→Bin : ℕ → Bin 
ℕ→Bin zero     = 0∎
ℕ→Bin (suc n) = sucBin (ℕ→Bin n) 

BinPos→ℕ : Pos → ℕ
BinPos→ℕ 1∎     = 1
BinPos→ℕ (`0 p) = BinPos→ℕ p + BinPos→ℕ p
BinPos→ℕ (`1 p) = 1 + (BinPos→ℕ p + BinPos→ℕ p)

Bin→ℕ : Bin → ℕ 
Bin→ℕ 0∎    = 0
Bin→ℕ (` p) = BinPos→ℕ p 
``` 

And witness an isomorphism:

(I left some holes because I'm lazy and this isn't really the point.)

```agda 
Bin→ℕ→Bin : ℕ→Bin ∘ Bin→ℕ ∼ id 
Bin→ℕ→Bin 0∎ = refl
Bin→ℕ→Bin (` p) = lemmaPos p
  where
  lemmaPos : (p : Pos) → ℕ→Bin (BinPos→ℕ p) ≡ (` p)
  lemmaPos 1∎     = refl
  lemmaPos (`0 p) with BinPos→ℕ p | lemmaPos p
  ... | zero | eq =  ⊥-elim (transport (ua (BinEqv 0∎ (` p)) ⁻¹) eq)
  ... | suc n | eq = {!   !}
  lemmaPos (`1 p) = {!   !} 

↻-suc-Bin→ℕ : Bin→ℕ ∘ sucBin ∼ suc ∘ Bin→ℕ 
↻-suc-Bin→ℕ 0∎ = refl
↻-suc-Bin→ℕ (` x) = {!  !}

ℕ→Bin→ℕ : Bin→ℕ ∘ ℕ→Bin ∼ id 
ℕ→Bin→ℕ zero = refl
ℕ→Bin→ℕ (suc n) = ↻-suc-Bin→ℕ (ℕ→Bin n) ○ ap suc (ℕ→Bin→ℕ n) 
``` 

This of course gives rise to an equivalence: 

```agda 
ℕ≃Bin : ℕ ≃ Bin 
ℕ≃Bin = isoToEquiv (iso ℕ→Bin Bin→ℕ Bin→ℕ→Bin ℕ→Bin→ℕ)
``` 

which, via univalence, gives rise to an identity:

```agda 
ℕ≡Bin : ℕ ≡ Bin 
ℕ≡Bin = ua ℕ≃Bin
``` 

### Tranporting addition and associativity 

As with Bool, we can transport entire functions along this equality.
For example, addition.

```agda 
_⊕_ : Bin → Bin → Bin 
_⊕_ = transport (λ i → ℕ≡Bin i → ℕ≡Bin i → ℕ≡Bin i) _+_ 

-- it works! 
_ : Two ⊕ Three ≡ Five 
_ = refl 
``` 

A peak under the hood shows that Cubical Agda is in fact 
computing *with respect to* isomorphism. 

```agda 
module _ (x y : Bin) where 

  -- The following computes definitionally
  underTheHood : x ⊕ y ≡ ℕ→Bin (Bin→ℕ x + Bin→ℕ y)
  underTheHood = refl 

  -- Because Bin→ℕ is a retraction of ℕ→Bin,
  -- we have that Bin→ℕ is effectively a monoid homormophism between
  --   (Bin, _⊕_) and (ℕ , +)
  Homomorphism : Bin→ℕ (x ⊕ y) ≡ Bin→ℕ x + Bin→ℕ y 
  Homomorphism = (ℕ→Bin→ℕ (Bin→ℕ x + Bin→ℕ y))
``` 

The finale is that, like with the Booleans, we may transport proofs from 
the unary representation---which is more amenable to reasoning---to 
the binary representation. For example, commutativity of addition 
on ℕ. 

The following code I wrote myself quickly---a skill being rapidly 
replaced by AI. 

```agda 
+-0 : ∀ n → n + 0 ≡ n 
+-0 zero = refl
+-0 (suc n) = cong suc (+-0 n) 

suc-distr : ∀ n m → suc (n + m) ≡ n + suc m 
suc-distr zero m = refl
suc-distr (suc n) m = cong suc (suc-distr n m) 

+-comm : forall (x y : ℕ) → x + y ≡ y + x 
+-comm zero y = +-0 y ⁻¹
+-comm (suc x) y = cong suc (+-comm x y) ○ suc-distr y x 
``` 

Now we may transport this proof to the binary representation.
Note first that we establish a **path** from `_+_` to `_⊕_`---
which states that the two are equivalent under ℕ≡Bin.
More specifically, there is a dependent path from `_+_` to `_⊕_`
under the family `λ i → ℕ≡Bin i → ℕ≡Bin i → ℕ≡Bin i`.

```agda
module TransportComm where 
  addp : PathP (λ i → ℕ≡Bin i → ℕ≡Bin i → ℕ≡Bin i) _+_ _⊕_ 
  addp i = transp (λ j → ℕ≡Bin (i ∧ j) → ℕ≡Bin (i ∧ j) → ℕ≡Bin (i ∧ j)) (~ i) _+_
``` 

The `addp` path lets us "switch" between `_+_` and `_⊕_`. That is, we have:
- `addp i₀ = _+_`
- `addp i₁ = _⊕_`

which lets us define a path from `x + y ≡ y + x` to `x ⊕ y ≡ y ⊕ x`. 
Note that, in the definition of the path `p`, we have 
- `addp i₀ x y = x + y`, and 
- `addp i₁ x y = x ⊕ y`

```agda 
  p : (∀ x y → x + y ≡ y + x) ≡ (∀ x y → x ⊕ y ≡ y ⊕ x)
  p i = (x y : ℕ≡Bin i) → addp i x y ≡ addp i y x 
``` 

Hence `p` has the correct endpoints. Transporting `+-comm` over `p` yields 
a proof that `_⊕_` is commutative.

```agda 
  ⊕-comm : forall (x y : Bin) → x ⊕ y ≡ y ⊕ x 
  ⊕-comm = transport p +-comm
``` 

## Some final thoughts

Throughout this note, I have invisibly transitioned between two contradictory assertions:
- Wow, transporting along an equality has *computational content*! 
- Which means So `x ⊕ y` definitionally equals `ℕ→Bin (Bin→ℕ x + Bin→ℕ y)`...
  which means that all of the complicated machinery we've used to transport
  along univalently-induced equalities could equally have been done traditionally.

The second argument is true, as well, for "transporting proofs". Which of these two "proofs" is simpler?

We have the univalent argument:

```agda 
module Proofs where 
  addp : PathP (λ i → ℕ≡Bin i → ℕ≡Bin i → ℕ≡Bin i) _+_ _⊕_ 
  addp i = transp (λ j → ℕ≡Bin (i ∧ j) → ℕ≡Bin (i ∧ j) → ℕ≡Bin (i ∧ j)) (~ i) _+_

  p : (∀ x y → x + y ≡ y + x) ≡ (∀ x y → x ⊕ y ≡ y ⊕ x)
  p i = (x y : ℕ≡Bin i) → addp i x y ≡ addp i y x 

  ⊕-comm₁ :  forall (x y : Bin) → x ⊕ y ≡ y ⊕ x  
  ⊕-comm₁ = transport p +-comm 
``` 

Or the straightforward argument:

```agda 
  ⊕-comm₂ :  forall (x y : Bin) → x ⊕ y ≡ y ⊕ x   
  ⊕-comm₂ x y = cong ℕ→Bin (+-comm (Bin→ℕ x) (Bin→ℕ y)) 
```   

These proofs do not appear to be definitionally equivalent; 
trying to normalize `⊕-comm₁ x y` causes my Agda to run indefinitely.
Certainly, viewing proofs as objects, we have that `⊕-comm₂` is much clearer,
and easier to reason about. (As an aside, both ℕ and Bin are **Sets**, so they observe 
the UIP---hence both proofs are *propositionally* equal.) 

That said, it's certainly valid to be skeptical. A logical counter-point is that 
the data types and proofs we've provided are quite simple; perhaps transporting
a more involved theorem is more convenient (or feasible) than its straightforward
counterpart. I haven't read all of Vezzosi et al, but I imagine they provide 
other examples that may not have more straightforward constructions.

# Works Cited 
- Andrea Vezzosi, Anders Mörtberg, Andreas Abel. Cubical Agda: A dependently typed programming language with univalence and higher inductive types. 
  - https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cubical-agda-a-dependently-typed-programming-language-with-univalence-and-higher-inductive-types/839F14B5227969B039D7B57AA8272C6B
