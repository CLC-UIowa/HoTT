# Errata for Rijke's Introduction to Homotopy Type Theory
These are the collected errors we (the Computational Logic Center at the University of Iowa) noticed during our seminar on Homotopy Type Theory, following the text in order.

Unfortunately, we performed exercises during the first semester (Part I: Ch. 1-8) largely on the board, and did not record any errata. Exercises for Part II have been mechanized in Agda, with errata noted.

*to be sent to egbert.rijke@fmf.uni-lj.si or to the homotopy type theory chat at https://hott.zulipchat.com. We may also share read access with Egbert for github.com/CLC-UIowa/HOTT-CLC-Fall-2025.*


## Chapter 9

### 9.3 (b)

The text for 9.3 (b) is somewhat misleading: "show that for any two homotopic equivalences e, e' : A \simeq B, their inverses are also homotopic", where the inverses of e an e' are their sections. This statement is not true! For example, consider the following two equivalences of the Boolean type.

```agda
  𝔹⁻¹ : Bool ≃ Bool
  𝔹⁻¹ = not , ((not , neg-bool-id) , (not , neg-bool-id))
  𝔹 : Bool ≃ Bool
  𝔹 = id , (id , refl-∼) , (id , refl-∼)
```

We think the question should be reworded to emphasize that, if e₁ and e₂ are equivalences built from (resp.) f and g such that
H : f ∼ g, then the sections of their equivalences are homotopic. (This statement is true.)

### 9.7 (e)

We are pretty certain this statement is false, and that α and β should have the following types:

```agda
α : B′ → is-equiv f
β : A′ → is-equiv g
```

(The text reads that α and β have domains B and A, respectively.) If one tries to solve the exercise as written, the (i) to (ii) case goes through, but the (ii) to (i) case is impossible.  To see that the (ii) to (i) case is impossible as written, first note that what is required is to produce functions from A' × B' to A × B.  All we have are the functions α and β, which (as written) require a B and an A, respectively, to be of any use to us.  But we only get to assume we have an element (a', b') : A' × B', and from this we cannot obtain an element of type B or an element of type A, so we are stuck.  Making the changes described above fixes the problem.

## Chapter 10

### 10.4.3 & 10.4.4

Less an error and more a matter of taste, but definitions 10.4.3 and 10.4.4 are arguably lemmas, not definitions. Def 10.4.3 is a claim (and proof) that if `f ∼ g`, then f and g are naturally isomorphic. Def 10.4.4 proves that `H ∘ f ∼ ap f ∘ H` if `f ∼ id`. Proofs of each are given in [`10/Reading.agda](./agda/Chapters/`10/Reading.agda).


### 10.8

The text gives
```agda
e : A ≃ Σ[ y ∈ B ] fib f y
```
but later (in particular, in the commutative diagram) uses `e` as a function
when `fst e` is probably what was intended.

## Chapter 14 


### 14.2

When describing the induction principle of the propositional truncation HIT, bullet point (ii) states that "This second 
requirement is therefore that
  
``` 
tr_P (\alpha(x, y), u) = v
```

but this should be `tr_Q`. 


### 14.4 

Theorem 14.4.6 describes the Kraus map as given by


``` 
g ↦ (g ∘ η , λ x y. ap g (α(x , y)))
``` 

But this should be:

``` 
g ↦ (g ∘ η , λ x y. ap g (α(η x, η y)))
``` 

(Note that x and y have type A, whereas α excepts inputs in the truncation of A.)

A separate remark: Given the definition of being *weakly constant* that precedes it, Theorem 14.4.6 could be rephrased as stating
that the witness to 

```
(∥ A ∥ → B) → Σ[ f ∈ (A → B) ] (weakly-constant f)
```

is an equivalence.

## Chapter 17
 
### Def 17.1.3

I believe the phrase "A type X is said to be 𝒰-small..." should be "A type A is said to be...". That is, the definition is defined in terms of A, not X.
