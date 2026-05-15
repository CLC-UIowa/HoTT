```
module Notes.FibersOverX where

open import Chapters.`09.Reading
open import Chapters.`10.Reading 
open import Chapters.`11.Reading
open import Prelude

private variable
  ℓ : Level
  A B C D : Set ℓ
```

The HoTT book describes:
  - A type family P : A → 𝒰 as a "fibration",
  - The type A as the "base space",
  - The type Σ A P as the "total space", and
  - The type P x as the "fiber over x" for x : A.

This wording is borrowed from topology in which we can think of 
some total space E sitting over top a base space B, with a canonical
projection function p : E → B.

     ---- 
  --  |  --
--    |    --
--    |    --  E
  --  |  -- 
    ----
      |
      | p
      V
      x
-------------------- B

Analogously, the "canonical projection function" for us type theorists
is π₁ : Σ A B → A. When we say that P x is the "fiber over x", we mean the *fiber of
π₁ at x*.

Let's prove that fib π₁ x ≃ P x.

```
module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) where
  fibOverX : ∀ (x : A) → fib (fst {B = P})  x ≃ P x
  fibOverX x = {!!} 
``` 
