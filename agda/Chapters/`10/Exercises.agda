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

  import Data.Unit

  {- 
  -- We will show that if A is contractible then (const tt) is an equivalence between A and ⊤.
  -- To do this we need to show that (const tt) has a section and that it has a retraction.
  -- A section of (const tt) is a function "f" of type (⊤ → A) that satisfies the property:
  --
  --     (const tt) ∘ f ~ id    Note that id is the identity on ⊤
  --
  -- To construct the function f we'll need a guarantee that A is a non-empty type.
  -- Thankfully since we know that A is contractible we know that it has a center of contraction.
  -- Let's call the center "c".
  -- Define
  -- 
  --     f := (const c)
  --
  -- The remainder of the proof is just computation i.e. refl.
  -}

  const-tt-has-section : {ℓ : Level} → {A : Set ℓ} → is-contr A → section {ℓ} {A} (const tt)
  const-tt-has-section (center , contraction) = const center , (λ x → refl)

  {- 
  -- Now let's show that (const tt) has a retraction.
  -- Remember that a retraction of (const tt) is a function h : ⊤ → A that satisfies:
  --
  --     h ∘ (const tt) ~ id    This time id is the identity on A
  --
  -- There aren't too many functions of the type (⊤ → A) so let's try to make 
  -- (const c) do double duty as a retraction.
  -- Recall that "c" is A's center of contraction.
  -- This time the remainder of the proof is not "just computation".
  -- To see why, let's simplify the goal manually:
  --
  --       (const c) ∘ (const tt) ~ id
  --     ⇐   const c (const tt a) ≡ id a    where "a" denotes an arbitrary A
  --     ⇐                      c ≡ a
  --
  -- We're fortunate that (c ≡ a) is the instantiation of A's contraction at element a.
  --
  -- *Bonus*.  This definition suggests that if we're given (const tt) : ⊤ → A 
  -- has a retraction then we can show A is contractible.
  -}

  const-tt-has-retraction : {ℓ : Level} → {A : Set ℓ} → is-contr A → retraction {ℓ} {A} (const tt)
  const-tt-has-retraction (center , contraction) = const center , contraction

  {- 
  -- We have all we need to show that (const tt) is an equivalence from A to ⊤.
  -}

  const-tt-is-equiv : {ℓ : Level} → {A : Set ℓ} → is-contr A → is-equiv {ℓ} {A} (const tt)
  const-tt-is-equiv is-contr-A = 
    ( const-tt-has-section is-contr-A , const-tt-has-retraction is-contr-A )

  {- 
  -- Now let's show that if (const tt) is an equivalence from A to ⊤ then A is a contractible type.
  -- Since (const tt) is an equivalence we know that it has both a retraction as well as a section.
  -- To show that A is contractible it should be enough to know that (const tt) has a retraction.
  -- The existence of the section is irrelevant at the moment.
  -- 
  -- Let's remind ourselves that a retraction of (const tt) is a function "h" : (⊤ → A) satisfying:
  --
  --     λ (a : A) → (h tt) ≡ a
  --
  -- Hmm, wouldn't everything fall into place if we chose (h tt) as A's center of contraction?
  -- Let's try that.
  -}

  A-is-contractible : {ℓ : Level} → {A : Set ℓ} → is-equiv {ℓ} {A} (const tt) → is-contr A
  A-is-contractible (_ , (h , h-is-retraction)) = (h tt , h-is-retraction)

  -------------------------------------------------------------------------------
  -- (b) Apply Exercise 9.4 to show that for any map f : A → B, if any two of the
  -- three assertions
  --   (i) A is contractible
  --   (ii) B is contractible
  --   (iii) f is an equivalence
  -- hold, then so does the third.

  {- 
  -- Let's start by showing that (i) and (ii) together imply (iii).
  --
  -- We know that both A and B are contractible.
  -- This means that A has a center "c-A" and for any "a" : A we have a proof that c_A ≡ a.
  -- Similarly B has a center "c-B" and for any "b" : B we have a proof that c_B ≡ b.
  -- Because each of A and B has a center we know both types a non-empty.
  --
  -- We want to show that f : A → B is an equivalence.
  -- We will show that f has a section as well as a retraction.
  -- Both the section as well as the retraction will have the type B → A.
  -- This hints that (const c_A) should be the section as well as the retraction.
  -- Let's confirm our guess by actually writing the proofs.
  -- 
  -- To start let's prove that (const c_A) is a section of f:
  --
  --       (f (const c_A b))        |          id b
  --     ≡ (f c_A)                  |        ≡ b
  -}

  

-------------------------------------------------------------------------------
-- #10.4 Show that Finₖ is not contractible for all k ≠ 1.

module 10-4 where
  private
    variable
      ℓ : Level

  fin-not-contractible : ∀ (n : ℕ) → ¬ is-contr (Fin (suc (suc n)))
  fin-not-contractible n (center , contraction) with ! (contraction fzero) ○ ((contraction (fsuc fzero)))
  ... | ()
