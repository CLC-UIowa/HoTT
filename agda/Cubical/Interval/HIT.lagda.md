```agda 
module Interval.HIT where 

open import Prelude.Paths
open Cubical
open GVars 
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

We can repeat the results from postulated 𝕀.

## 𝕀 is contractible 

Note that the cubical library has its own definition of contractibility, `isContr`.

```agda 
contr : isContr 𝕀 
contr = i₀ , {!   !} 
  where 
    f : (j : 𝕀) → i₀ ≡ j
    f i₀ = refl
    f i₁ = seg
    f (seg i) j = {!   !} 
``` 


## 𝕀 implies functional extensionality 

```agda 

fun-ext : {f g : A → B} → f ∼ g → f ≡ g 
fun-ext H = {!  !} 

