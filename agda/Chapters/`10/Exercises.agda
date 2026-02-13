module Chapters.`10.Exercises where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`10.Reading

-- open HomReasoning

-------------------------------------------------------------------------------
-- #10.1 Show that if A is contractible, then for any x, y : A the identity
-- type x ≡ y is also contractible.

module 10-1 where
  private
    variable
      ℓ : Level

-------------------------------------------------------------------------------
-- #10.2 Suppose that A is a retract of B. Show that
--   is-contr(B) → is-Contr(A)

module 10-2 where
  private
    variable
      ℓ : Level
  open PathReasoning

  -- We have that A is a retract of B, there is an f : A → B such that f is a retraction.
  -- Since f is a retraction, we can obtain f-retr : B → A and f-retr-h : f-retr ∘ f ∼ id.
  -- Now, as B is contractible, we have a center b : B and a contraction eq-b : ∀ (x : B) → b ≡ x.
  -- We want to construct center : A and contraction : ∀ (x : A) → center = x.
  --
  -- The only way we have to construct an element of A is via f-retr, and the only element of B we have
  -- to feed f-retr is b.
  -- So we let center = f-retr b.
  --
  -- For the proof, we chain ≡ reasoning.
  -- Fix a : A.
  -- As b is the center of B, we have that
  --   f-retr b ≡ f-retr (f a).
  -- Finally, since f is a retraction with f-retr being the associated pseudo-inverse, we have
  --   f-retr (f a) = a. ∎
  retract-is-contractible : {A : Set ℓ} {B : Set ℓ} → (f : A → B) → (retraction {A = A} {B = B} f) → is-contr B → is-contr A
  retract-is-contractible {A = A} {B = B} f (f-retr , f-retr-h) (b , eq-b) = center , contraction
    where
      center : A
      center = f-retr b

      contraction : (a : A) → f-retr b ≡ a
      contraction a = begin
        f-retr b ≡⟨ (ap f-retr $ eq-b $ f a) ⟩
        f-retr (f a) ≡⟨ f-retr-h a ⟩
        a ∎

-------------------------------------------------------------------------------
-- #10.3

module 10-3 where
  private
    variable
      ℓ : Level

  -------------------------------------------------------------------------------
  -- (a) Show that for any type A, the map const_* : A → 1 is an equivalence
  --     iff A is contractible.

  -------------------------------------------------------------------------------
  -- (b) Apply Exercise 9.4 to show that for any map f : A → B, if any two of the
  -- three assertions
  --   (i) A is contractible
  --   (ii) B is contractible
  --   (iii) f is an equivalence
  -- hold, then so does the third.

-------------------------------------------------------------------------------
-- #10.4 Show that Finₖ is not contractible for all k ≠ 1.

module 10-4 where

  ez-proof : ∀ (n : ℕ) → ¬ is-contr (Fin (suc (suc n)))
  ez-proof n  (center , contraction) 
    with ! (contraction fzero) ○ ((contraction (fsuc fzero)))
  ... | ()

  -- Here is how you prove disjointedness of constructors 
  -- fzero & fsuc fzero without relying on the empty pattern.
  -- This more closely resembles (but is still not exactly)
  -- the proof Rijker would have had in mind using the book's
  -- def'n of Fin.
  fzero≠fone : ∀ {n} → ¬ (fzero ≡ fsuc {n = suc n} fzero) 
  fzero≠fone eq = tr I eq tt 
    where
      I : ∀ {n} → Fin (suc (suc n)) → Set
      I fzero        = ⊤ 
      I (fsuc fzero) = ⊥ 
      I _            = ⊤

  fin-not-contractible : ∀ (n : ℕ) → ¬ is-contr (Fin (suc (suc n)))
  fin-not-contractible n (center , contraction) = fzero≠fone bad 
    where
      bad : fzero ≡ fsuc fzero 
      bad = ! (contraction fzero) ○ ((contraction (fsuc fzero)))

