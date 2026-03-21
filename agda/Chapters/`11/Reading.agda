module Chapters.`11.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`10.Reading

-- open HomReasoning
--------------------------------------------------------------------
-- Chapter 11: The fundamental theorem of identity types


private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B D X Y Z : Set ℓ
    𝐁 𝐂 𝐃 : A → Set ℓ
    f g h i : (x : A) → 𝐁 x


--------------------------------------------------------------------
-- §11.1: Families of equivalences

-- Def 11.1.1
tot : (∀ (x : A) → 𝐁 x → 𝐂 x) → Σ A 𝐁 → Σ A 𝐂
tot f (x , y) = x , f x y


-- Lemma 11.1.2 For any family of maps 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 and any
-- 𝑡 : Σ_(𝑥:𝐴) 𝐶 𝑥, there is an equivalence
-- fib_(tot f) (t) ≃ fib_(f (pr₁ t)) (pr₂ t)

fib-tot-equiv : (f : ∀ (x : A) → 𝐁 x → 𝐂 x) → (t : Σ A 𝐂) → fib (tot f) t ≃ fib (f (fst t)) (snd t)
fib-tot-equiv f t = ϕ , ϕ-is-equiv
  where
  ϕ : fib (tot f) t → fib (f (fst t)) (snd t)
  ϕ ((x , y) , refl) = y , refl

  ψ : fib (f (fst t)) (snd t) → fib (tot f) t
  ψ (y , refl) = ((fst t) , y) , refl


  G-hom : ϕ ∘ ψ  ∼ id
  G-hom (y , refl) = refl

  H-hom : ψ ∘ ϕ  ∼ id
  H-hom (x , refl) = refl

  ϕ-is-equiv : is-equiv ϕ
  ϕ-is-equiv = (ψ , G-hom) , (ψ , H-hom)

-- lemma 11.1.3
-- let 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 be a family of maps
-- The following are equivalent
-- (i) for each x the map f x is an equivalence. We call f a _family of equivalences_
-- (ii) The map tot (f) : Σ_(x : A) B x -> Σ_(x : A)  C x is an equivalence
