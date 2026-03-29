module Chapters.`11.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`10.Reading
open import Chapters.`10.Exercises

-- open HomReasoning
--------------------------------------------------------------------
-- Chapter 11: The fundamental theorem of identity types


private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B D X Y Z : Set ℓ
    -- 𝐁 𝐂 𝐃 : A → Set ℓ
    -- f g h i : (x : A) → 𝐁 x


--------------------------------------------------------------------
-- §11.1: Families of equivalences

-- Def 11.1.1
tot : {𝐁 𝐂 : A → Set ℓ} → (∀ (x : A) → 𝐁 x → 𝐂 x) → Σ A 𝐁 → Σ A 𝐂
tot f (x , y) = x , f x y


-- Lemma 11.1.2 For any family of maps 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 and any
-- 𝑡 : Σ_(𝑥:𝐴) 𝐶 𝑥, there is an equivalence
-- fib_(tot f) (t) ≃ fib_(f (pr₁ t)) (pr₂ t)

fib-tot-equiv : {𝐁 𝐂 : A → Set ℓ} → (f : ∀ (x : A) → 𝐁 x → 𝐂 x) → (t : Σ A 𝐂) → fib (tot f) t ≃ fib (f (fst t)) (snd t)
fib-tot-equiv f t = ϕ , ϕ-is-equiv
  where
  ϕ : fib (tot f) t → fib (f (fst t)) (snd t)
  ϕ ((x , y) , refl) = y , refl

  ψ : fib (f (fst t)) (snd t) → fib (tot f) t
  ψ (y , refl) = ((fst t) , y) , refl


  𝔾 : ϕ ∘ ψ  ∼ id
  𝔾 (y , refl) = refl

  ℍ : ψ ∘ ϕ  ∼ id
  ℍ (x , refl) = refl

  ϕ-is-equiv : is-equiv ϕ
  ϕ-is-equiv = (ψ , 𝔾) , (ψ , ℍ)

-- lemma 11.1.3
-- let 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 be a family of maps
-- The following are equivalent
-- (i) for each x the map f x is an equivalence. We call f a _family of equivalences_
-- (ii) The map tot (f) : Σ_(x : A) B x -> Σ_(x : A)  C x is an equivalence
module 11•1•3 {A : Set ℓ} {𝐁 𝐂 : A → Set ℓ} (f : (x : A) → 𝐁 x → 𝐂 x) where
  -- is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b)
  -- 10.3.5 is-contr-map-equiv (f : A → B) : is-contr-map f → is-equiv f
  -- thm•10•4•6 (f : A → B) : is-equiv f → is-contr-map f


  lem : (x : A) (c : 𝐂 x) → fib (tot f) (x , c) ≃ fib (f x) c
  lem x c = fib-tot-equiv f (x , c) -- lemma 11•1•2

  lem0 : (x : A) (c : 𝐂 x) → is-contr (fib (tot f) (x , c)) ↔ is-contr (fib (f x) c)
  lem0 x c with lem x c
  ... | (ϕ , ϕ-is-equiv) =
      (λ p → 10-3.ex-10-3-i-iii⇒ii ϕ p ϕ-is-equiv) , λ p → 10-3.ex-10-3-ii-iii⇒i ϕ p ϕ-is-equiv

  thm : (x : A) → is-equiv (f x) ↔ is-equiv (tot f)
  thm x = {!!}

-- Lemma 11.1.4
-- Consider a map 𝑓 : 𝐴 → 𝐵, and let 𝐶 be a type family over 𝐵.
-- If 𝑓 is an equivalence,then the map
--       σ_f (𝐶) : λ (x, z). (f x, z) : Σ_{x: A} 𝐶 (f x) → Σ_{y: B} 𝐶 (y)
-- is and equivalence
module 11•1•4 {A B : Set ℓ} {𝐂 : B → Set ℓ}(f : A → B) where
  -- We first define the map σ
  σ : Σ[ x ∈ A ] (𝐂 (f x)) → Σ[ y ∈ B ] 𝐂 y
  σ (x , z) =  f x , z

  -- Now we show that the fibers of σ and f at t are equivalent,
  -- i.e. fib σ t ≃ fib f (pr₁ t)
  ϕ : (t : Σ[ y ∈ B ] (𝐂 y)) → fib σ t → fib f (fst t)
  ϕ ( y , z) ((x , z) , refl) = x , refl

  ψ : (t : Σ[ y ∈ B ] (𝐂 y)) → fib f (fst t) → fib σ t
  ψ (y , z) (x , refl) = (x , z) , refl

  𝔾 : (t : Σ[ y ∈ B ] (𝐂 y)) → ϕ t ∘ ψ t ∼ id
  𝔾 (y , z) (x , refl) = refl

  ℍ : (t : Σ[ y ∈ B ] (𝐂 y)) → ψ t ∘ ϕ t ∼ id
  ℍ (y , z) ((x , z) , refl) = refl

  lem0 : (t : Σ[ y ∈ B ] (𝐂 y)) → fib σ t ≃ fib f (fst t)
  lem0 t = ϕ t , ((ψ t , 𝔾 t) , ψ t , ℍ t)

  -- we show that σ is equivalent if and only if ϕ is a contractible map
  lem : is-equiv f → is-equiv σ
  lem is-equiv-f = {!11•1•3.def !}

-- Definition 11.1.5
-- Consider a map f : A → B and a family of maps
--     g : (x : A) → C x → D (f x)
-- where C is a type family over A and D is a type family over B.
-- We define tot_f g : Σ_{x : A} C x → Σ_{y:B} D y
-- we say g is a family of maps over f

In_familyOfMapsOver_Is_ : {𝐂 : A → Set ℓ} (𝐃 : B → Set ℓ) (f : A → B) (g : (x : A) → 𝐂 x → 𝐃 (f x))
     → Σ A 𝐂  → Σ[ y ∈ B ] (𝐃 y)
In 𝐃 familyOfMapsOver f Is g = λ (x , z) → (f x , g x z)


-- Theorem 11.1.6
-- suppose g is a family of maps over f,
-- then the following are equivalent
-- (i) The family of maps g over f is a family of equivalences
-- (ii) the map tot_f (g) is an equivalence
module 11•1•6 {𝐂 : A → Set ℓ}(𝐃 : B → Set ℓ) (f : A → B) (g : (x : A) → 𝐂 x → 𝐃 (f x)) where
  thm : is-equiv (tot g) ↔ is-equiv (In 𝐃 familyOfMapsOver f Is g)
  thm = {!!}


-- § 11.2 The fundamental theorem
-- The fundamental theorem describes what are the necessary and sufficient conditions on a type family 𝐁
-- over a type A equipped with a point a : A
-- to obtain an equivalence (a ≡ x) ≃ 𝐁 x for each x : A
