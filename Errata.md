# Errata for Rijke's Introduction to Homotopy Type Theory
These are the collected errors we (the Computational Logic Center at the University of Iowa) during our seminar on Homotopy Type Theory, following the text in order.

Unfortunately, we performed exercises during the first semester (Part I: Ch. 1-8) largely on the board, and did not record any errata. Exercises for Part II have been mechanized in Agda, with errata noted.

*to be sent to egbert.rijke@fmf.uni-lj.si or to the homotopy type theory chat at https://hott.zulipchat.com. We may also share read access with Egbert for github.com/CLC-UIowa/HOTT-CLC-Fall-2025.*


## Chapter 9

### 9.3 (b)

THe text for 9.3 (b) is somewhat misleading: "show that for any two homotopic equivalences e, e' : A \simeq B, their inverses are also homotopic", where the inverses of e an e' are their sections. This statement is not true! For example, consider the following two equivalences of the Boolean type.

```agda
  𝔹⁻¹ : Bool ≃ Bool
  𝔹⁻¹ = not , ((not , neg-bool-id) , (not , neg-bool-id))
  𝔹 : Bool ≃ Bool
  𝔹 = id , (id , refl-htpy _) , (id , refl-htpy _)
```

We think the question should be reworded to emphasize that, if e₁ and e₂ are equivalences built from (resp.) f and g such that
H : f ∼ g, then the sections of their equivalences are homotopic. (This statement is true.)

### 9.7 (e)

We are pretty certain this statement is false, and that \alpha and \beta should have the following types:

```agda
α : B′ → is-equiv f
β : A′ → is-equiv g
```

(The text reads that \alpha and \beta have domains B and A, respectively.) If one tries to solve the exercise as written, the (i) to (ii) case goes through, but the (ii) to (i) case is impossible.
To see that the (ii) to (i) case is impossible as written, first note that what is required is to produce functions from A' \times B' to A \times B.
All we have at our disposable are the functions \alpha and \beta, which (as written) require a B and an A, respectively, to be of any use to us.
But we only get to assume we have an element (a', b') : A' \times B', and from this we cannot obtain an element of type B or an element of type A, so we are stuck.
Making the changed described above fixes the problem.
