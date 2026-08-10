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
      A : Set ℓ
  open PathReasoning
  ex-10-1 : ∀ {A} (x y : A) → is-contr {ℓ = ℓ} A → is-contr (x ≡ y)
  ex-10-1 {A = A} x y (cA , C) = center-x≡y , λ { refl → left-inv (C x)  }
    where
      center-x≡y : x ≡ y
      center-x≡y = (C x) ⁻¹ ○ C y

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
  retract-is-contractible : ∀ {ℓ₁ ℓ₂} → 
                              {A : Set ℓ₁} {B : Set ℓ₂} → 
                              (f : A → B) → (retraction {A = A} {B = B} f) → is-contr B → is-contr A
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
      A B : Set ℓ
  import Data.Unit
  open import Chapters.`09.Exercises

  -------------------------------------------------------------------------------
  -- (a) Show that for any type A, the map const_* : A → 1 is an equivalence
  --     iff A is contractible.

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

  const-tt-has-section :  is-contr A → section (λ (x : A) → tt)
  const-tt-has-section (center , contraction) = const center , (λ { tt → refl })

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

  const-tt-has-retraction : is-contr A → retraction (λ (x : A) → tt)
  const-tt-has-retraction (center , contraction) = const center , contraction

  {-
  -- We have all we need to show that (const tt) is an equivalence from A to ⊤.
  -}

  const-tt-is-equiv : is-contr A → is-equiv (λ (x : A) → tt)
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

  A-is-contractible : is-equiv (λ (x : A) → tt) → is-contr A
  A-is-contractible (_ , (h , h-is-retraction)) = (h tt , h-is-retraction)

  -------------------------------------------------------------------------------
  -- (b) Apply Exercise 9.4 to show that for any map f : A → B, if any two of the
  -- three assertions
  --   (i) A is contractible
  --   (ii) B is contractible
  --   (iii) f is an equivalence
  -- hold, then so does the third.

  {-
  -- We'll describe two proofs that (i) and (ii) together imply (iii).
  --
  -- First proof
  -- ===========
  --
  -- This approach doesn't rely on exercise 9.4.
  --
  -- We know that both A and B are contractible.
  -- This means that A has a center "a" and for all "x" : A we know that (a ≡ x)
  -- Similarly B has a center "b" and for all "y" : B we know that (b ≡ y).
  -- Let's take a moment to note that both A and B are non-empty.
  --
  -- We want to show that f : A → B is an equivalence.
  -- We will show that f has a section as well as a retraction.
  -- Both the section as well as the retraction are of type B → A.
  -- (const a) which is perhaps the only function of type B → A we can construct
  -- is very likely both a section and a retraction of f.
  -- Let's confirm our guess by actually writing the proofs.
  --
  -- To start let's prove that (const a) is a section of f:
  --
  --       (f (const a y))        |          id y
  --     ≡ (f a)                  |        ≡ y
  --
  -- The contraction for B tells us (b ≡ f a) as well as (b ≡ y).
  -- The equality we need follows from symmetry and transitivity of ≡.
  --
  -- Let's prove that (const a) is also retraction of f:
  --
  --       const a (f x)          |         id x
  --     ≡ a                      |       ≡ x
  --
  -- The contraction for A tells us (a ≡ x) -- exactly what we need.
  --
  -- Second proof
  -- ============
  --
  -- Once again, we know that both A and B are contractible and we want to prove
  -- that an arbitrary function f : A → B is an equivalence.
  --
  -- According to the statement of 9.4 (a), if we have a triangle:
  --
  --        w
  --     X ---> Y    where u ~ v ∘ w (the triangle commutes),
  --    u \   / v      and w has a section,
  --       v v         and v has a section,
  --        Z         then u also has a section.
  --
  -- Then according to the statement of 9.4 (b) for the same triangle:
  --
  --
  --                   if v has a retraction,
  --                  and w has a retraction,
  --                 then u has a retraction.
  --
  --
  -- We instantiate the triangle in a way that allows us to substitute the
  -- argument f in place of u.
  -- This way we'll be able to show that f has a section and f has a retraction.
  --
  --      ka := const tt
  --     A ----------> ⊤
  --      \           /      r := `retr kb
  --     f \         / where kb := const tt
  --        '-> B <-'
  --
  -- In the last part of this exercise we proved that a type X is contractible
  -- iff (const tt) : X → ⊤ is an equivalence.
  -- A and B are both contractible so ka = (const tt) : A → ⊤ and
  -- kb = (const tt) : B → ⊤ are equivalences.
  -- Let r denote (`retr kb) : ⊤ → B, the retraction used to prove that
  -- kb : B → ⊤ is an equivalence.
  -- Note that:
  --
  -- * f ~ r ∘ ka because B is contractible.
  -- * ka has a section because it is an equivalence.
  -- * r has a section because r is an equivalence.
  -- r is an equivalence because it is a retraction of the equivalence kb.
  -- See 9.4 (c) (ii) "any section and any retraction of an equivalence is again
  -- an equivalence."
  --
  -- By the statement of 9.4 (a), f has a section.
  --
  -- To see that f has a retraction by the statement of 9.4 (b), note that:
  --
  -- * r has a retraction because it is an equivalence.
  -- * ka has a retraction because it is an equivalence.
  --
  -- f has a section.  f has a retraction.  f is an equivalence.  Done!
  -}

  f-section↔g-section = 9-4.9-4a.f-section↔g-section
  f-retraction↔h-retraction = 9-4.9-4b.f-retraction↔h-retraction

  
  contr-domains⇒is-equiv : (f : A → B) →  is-contr A → is-contr B → is-equiv f
  contr-domains⇒is-equiv {A = A} {B = B} f (a , prf-cA) (b , prf-cB)  = f-sec , f-retr
    where
      is-equiv-const-tt-B : is-equiv {A = B} (const tt)
      is-equiv-const-tt-B = const-tt-is-equiv (b , prf-cB)

      is-equiv-const-tt-A : is-equiv {A = A} (const tt)
      is-equiv-const-tt-A = const-tt-is-equiv (a , prf-cA)

      prf-hom1 : f ∼ `retr is-equiv-const-tt-B ∘ const tt
      prf-hom1 = sym ∘ prf-cB ∘ f


      g-sec→f-sec = _↔_.from $ f-section↔g-section f (const tt) (`retr is-equiv-const-tt-B) prf-hom1
                             (fst is-equiv-const-tt-A)


      prf-hom2 : f ∼ `retr is-equiv-const-tt-B ∘ const tt
      prf-hom2 = sym ∘ prf-cB ∘ f

      h-ret→f-ret = _↔_.from $ f-retraction↔h-retraction f (const tt) (`sec is-equiv-const-tt-B) prf-hom2
                  (const tt , λ { tt → refl })

      f-sec : section f
      f-sec = g-sec→f-sec  (const tt , prf-cB)

      f-retr : retraction f
      f-retr =  h-ret→f-ret (snd is-equiv-const-tt-A)

  lem : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B) → (eq-f : is-equiv f) → retraction (`sec eq-f)
  lem f eq-f = f , (eq-f .fst .snd)

  {-
  -- We want to show that if A is contractible and if f is a equivalence from A
  -- to B then B is contractible as well.
  --
  -- Exercise 10.2 will help us here: if B is a retract of A and A is
  -- contractible then B is contractible as well.  Recall that "B is a retract
  -- of A" means there exists some retraction (A → B) of some B → A function.
  --
  -- f has a section because it is an equivalence.
  -- B is a retract of A because f is a retraction of that section.
  -- We already know A is contractible.
  -- Exercise 10.2 allows us to conclude that B is contractible.
  -}

  contr-domain⇒contr-codomain : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                                 (f : A → B) →  
                                 is-contr A → is-equiv f → is-contr B
  contr-domain⇒contr-codomain {A = A} {B = B} f ctr-A eq-f = 10-2.retract-is-contractible (`sec eq-f) (lem f eq-f) ctr-A
  
  {-
  -- A is a retract of B because f : A → B is an equivalence and therefore has a
  -- retraction.
  -- We're given that B is contractible.
  -- Use exercise 10.2 to conclude that A is contractible.
  -}

  contr-codomain⇒contr-domain : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                                   (f : A → B) →  is-contr B → is-equiv f → is-contr A
  contr-codomain⇒contr-domain {A = A} {B = B} f ctr-B eq-f = 10-2.retract-is-contractible f (snd eq-f) ctr-B

open 10-3 hiding (lem) public 
  
-------------------------------------------------------------------------------
-- #10.4 Show that Finₖ is not contractible for all k ≠ 1.

module 10-4 where

  ez-proof : ∀ (n : ℕ) → ¬ is-contr (Fin (suc (suc n)))
  ez-proof n  (center , contraction)
    with (contraction fzero) ⁻¹ ○ ((contraction (fsuc fzero)))
  ... | ()

  -- Here is how you prove disjointedness of constructors
  -- fzero & fsuc fzero without relying on the empty pattern.
  -- This more closely resembles (but is still not exactly)
  -- the proof Rijke would have had in mind using the book's
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
      bad = (contraction fzero) ⁻¹ ○ ((contraction (fsuc fzero)))

-------------------------------------------------------------------------------
-- #10.5

module 10-5 where
{-  Show that for any two types A and B, the following are equivalent
  (i) Both A and B are contractible
  (ii) The type A × B is contractible
-}
  private
    variable
      ℓ : Level
      A B : Set ℓ
  open PathReasoning

  10-5-i⇒ii : is-contr A × is-contr B → is-contr (A × B)
  10-5-i⇒ii ((cA , contrA) , (cB , contrB)) = (cA , cB) ,
    λ { (x , y) → begin
           (cA , cB) ≡⟨  ap (_, cB) (contrA x) ⟩
           (x , cB) ≡⟨  ap (x ,_)  (contrB y)  ⟩
           (x , y) ∎ }

  10-5-ii⇒i : is-contr (A × B) → is-contr A × is-contr B
  10-5-ii⇒i {A = A}{B = B}(cAB , contrAB) = contr-A , contr-B
    where
    cA : A
    cA = fst cAB
    cB : B
    cB = snd cAB
    lem : cAB ≡ (cA , cB)
    lem = refl
    contr-A : is-contr A
    contr-A = cA , λ a → begin
      cA ≡⟨ ap fst (lem ⁻¹ ○ contrAB (a , cB)) ⟩
      a ∎

    contr-B : is-contr B
    contr-B = cB , λ b → begin
      cB ≡⟨ ap snd  (lem ⁻¹ ○ contrAB (cA , b)) ⟩
      b ∎

-----------------------------------------------------------------------------
-- #10.6

-- Let A be a contractible type with center of contraction a : A. Furthermore,
-- let B be a type family over A> Show that the map:
--    y ↦ (a , y) : B(a) → Σ_{x : A} B(x)
-- is an equivalence.

module 10-6 where
  private
    variable
      ℓ : Level
      A : Set ℓ
      B : A → Set ℓ
  open PathReasoning
  open import Agda.Builtin.Sigma
  import Relation.Binary.PropositionalEquality using (cong₂)

  f : (a : A) → B a → (Σ[ x ∈ A ] (B x))
  f a y = (a , y)

  f-retr : (A-is-contr : is-contr A) → retraction {A = B (is-contr.center A-is-contr)} {B = Σ[ x ∈ A ] (B x) } (f (is-contr.center A-is-contr))
  f-retr {A = A} {B = B} A-is-contr = g , λ (y : (B a)) → begin
    (g (f (is-contr.center A-is-contr) y)) ≡⟨ refl ⟩
    (g (a , y)) ≡⟨ refl ⟩
    (tr B ((C' a) ⁻¹) y) ≡⟨ ap (λ (h : a ≡ a) → tr B (h ⁻¹) y) p ⟩
    (tr B (refl ⁻¹) y) ≡⟨ refl ⟩
    (tr B refl y) ≡⟨ refl ⟩
    y ≡⟨ refl ⟩
    id y ∎
    where
      a : A
      a = is-contr.center A-is-contr
      C : (x : A) → a ≡ x
      C = is-contr.contraction A-is-contr
      C' : (x : A) → a ≡ x
      C' x = ((C a) ⁻¹) ○ C x
      p : C' a ≡ refl
      p = left-inv (C a)
      g : Σ[ x ∈ A ] (B x) → (B a)
      g = (λ{ (x , p) → tr B (((C' x) ⁻¹)) p})

  f-section : (A-is-contr : is-contr A) → section {A = B (is-contr.center A-is-contr)} {B = Σ[ x ∈ A ] (B x) } (f (is-contr.center A-is-contr))
  f-section {A = A} {B = B} (a , C) = h , λ { ((x , y)) → helper (x , y) (C' x) }
  -- begin
    -- f (is-contr.center A-is-contr) (h (x , y)) ≡⟨ refl ⟩
    -- f a (h (x , y)) ≡⟨ refl ⟩
    -- f a (tr B (! C' x) y) ≡⟨ refl ⟩
    -- (a , (tr B (! C' x) y)) ≡⟨ {!   !} ⟩
    -- (x , (tr B (! C' a) y)) ≡⟨ ? ⟩
    -- (a , (tr B (! C' a) (snd x))) ≡⟨ ? ⟩
    -- ((fst x) , (tr B (! C' (fst x)) (snd x))) ≡⟨ ? ⟩
    -- id (x , y) ∎ }

    where
      -- a : A
      -- a = is-contr.center A-is-contr
      -- C : (x : A) → a ≡ x
      -- C = is-contr.contraction A-is-contr
      C' : (x : A) → a ≡ x
      C' x = ((C a) ⁻¹) ○ C x
      p : C' a ≡ refl
      p = left-inv (C a)
      h : Σ[ x ∈ A ] (B x) → (B a)
      h = (λ{ (x , p) → tr B (((C' x) ⁻¹)) p})
      helper : (arb : Σ[ x ∈ A ] (B x)) → (p' : a ≡ (fst arb)) → (f a) (h arb) ≡ arb
      helper (x , y) refl = begin
        f x (h (x , y)) ≡⟨ refl ⟩
        (x , h (x , y)) ≡⟨ refl ⟩
        (x , tr B ((C' a) ⁻¹) y) ≡⟨ ap (λ h → (x , tr B (h ⁻¹) y)) p ⟩
        (x , tr B (refl ⁻¹) y) ≡⟨ refl ⟩
        (x , tr B refl y) ≡⟨ refl ⟩
        (x , y) ∎

  f-equivalence : (A-is-contr : is-contr A) → is-equiv {A = B (is-contr.center A-is-contr)} {B = Σ[ x ∈ A ] (B x) } (f (is-contr.center A-is-contr))
  f-equivalence = λ A-is-contr → f-section A-is-contr , f-retr A-is-contr



-------------------------------------------------------------------------------
-- #10.7
--
-- Let B be a family of types over A, and consider the projection map
--   prj₁ : (Σ_{x : A} B(x)) → A
--   (a) Show that for an a : A, the map
--         λ((x , y), p). tr B (p , y) : fib pr₁ a → B a
--       is an equivalence
--   (b) Show that the following are equivalent:
--       (i) The projection map pr₁ is an equivalence
--       (ii) The type B(x) is contractible for each x : A.
--   (c) Consider a dependent function b : Π (x : A) (B (x)). Show that the following
--       are equivalent:
--         (i) The map
--               λ x. (x , b(x)) : A → Σ_{x : A} B(x)
--             is an equivalence.
--         (ii) The type B(x) is contractible for each x : A.

module 10-7 where
  private
     variable
        ℓ : Level
        A : Set ℓ
        B : A → Set ℓ

  pr₁ : Σ[ x ∈ A ] (B x) → A
  pr₁ = fst

  module 10-7a where

    f : (a : A) → fib pr₁ a → B a
    f  {A = A} {B = B} a ((x , y), p) = tr B p y

    is-equiv-f : (a : A) → is-equiv (f {A = A} {B = B} a)
    is-equiv-f {A = A} a = section-f , retraction-f
      where
        inv-f : (a : A) → B a → fib (pr₁ {A = A} {B = B}) a
        inv-f {A} {B = B} a y = ((a , y) , refl)

        section-f : section (f a)
        section-f = (inv-f a) , refl-∼

        infix 4 _≡f_
        _≡f_ : fib (pr₁ {A = A} {B = B}) a → fib (pr₁ {A = A} {B = B}) a → Set _
        _≡f_ = _≡_
        {-
        -- Proving this with just ind≡ is not fun.
        --
        -- inv-f∘f∼id : (inv-f a) ∘ (f a) ∼ id
        -- inv-f∘f∼id ((x , y) , p) =
        --     begin
        --       (inv-f a ∘ f a) ((x , y) , p)
        --     ≡⟨ induction ⟩
        --       ((x , tr B (! p) (tr B p y)) , ! (! p))
        --     ≡⟨ cong₂ (λ y' p' → (x , y') , p')
        --              (round-trip p)
        --              (involution p) ⟩
        --       ((x , y) , p) ∎
        --   where
        --     induction : (inv-f a ∘ f a) ((x , y) , p) f≡
        --                 ((x , tr B (! p) (tr B p y)) , ! (! p))
        --     induction = let motive x' p' =
        --                       (inv-f a ∘ f a) ((x , y) , p) f≡
        --                       ((x' , tr B p' (tr B p y)) , ! p')
        --                  in ind≡ a motive refl x (! p)
        --
        --     round-trip : tr B (! p) (tr B p y) ≡ y
        --     round-trip = let motive x' p' = tr B (! p') (tr B p' y) ≡ y
        --                   in ind≡ x motive refl a p
        --
        -- I have used a neater approach below.
        -}

        inv-f∘f∼id : (inv-f a) ∘ (f a) ∼ id
        inv-f∘f∼id ((x , y) , p) = inv-f∘f∼id-lemma p
          where inv-f∘f∼id-lemma :
                  (p' : x ≡ a) →
                  (inv-f a ∘ f a) ((x , y) , p') ≡f ((x , y) , p')
                inv-f∘f∼id-lemma refl = refl

        retraction-f : retraction (f a)
        retraction-f = (inv-f a) , inv-f∘f∼id

  module 10-7b where

--   (b) Show that the following are equivalent:
--       (i) The projection map pr₁ is an equivalence
--       (ii) The type B(x) is contractible for each x : A.

    open PathReasoning
    i⇒ii-lemma : (is-equiv (pr₁ {A = A} {B = B})) → (x : A) → is-contr (fib (pr₁ {B = B}) x)
    i⇒ii-lemma {A = A} {B = B} pr-equiv x = is-equiv⇒is-contr-map (pr₁ {A = A} {B = B}) pr-equiv x

    i⇒ii : (is-equiv (pr₁ {A = A} {B = B})) → (x : A) → is-contr (B x)
    i⇒ii {A = A} {B = B} is-equiv-pr x with i⇒ii-lemma is-equiv-pr x
    ... | ((a , b) , refl) , ctr-prf = b , λ b' → lem (ctr-prf ((x , b') , refl))

      where
        lem : ∀ {a x : A} {b : B a} {b' : B x} {a≡x} ->  _≡_ {A = fib (pr₁ {B = B}) x} ((a , b) , a≡x) ((x , b') , refl) → tr B a≡x b ≡ b'
        lem refl = refl


    ii⇒i : (all-is-contr : (x : A) → is-contr (B x)) → is-equiv (pr₁ {A = A} {B = B})
    ii⇒i {A = A} {B = B} all-is-contr = (sec ,  sec-h) , (retr , retr-h)
      where
        center-B : (a : A) → B a
        center-B a = is-contr.center (all-is-contr a)

        contraction-B : (a : A) → (b : B a) → (center-B a ≡ b)
        contraction-B a = is-contr.contraction (all-is-contr a)

        sec : A → Σ A B
        sec a = a , (center-B a)

        sec-h : pr₁ ∘ sec ∼ id
        sec-h = refl-∼

        retr : A → Σ A B
        retr = sec

        retr-h : retr ∘ pr₁ ∼ id
        retr-h (a , b) = ind≡ (center-B a) (λ b' eq → (a , center-B a) ≡ (a , b')) refl b (contraction-B a b)
        -- Or we can pattern match
        -- retr-h (a , b) with (contraction-B a b)
        -- ... | refl = refl


  module 10-7c where
--   (c) Consider a dependent function b : Π (x : A) (B (x)). Show that the following
--       are equivalent:
--         (i) The map
--               λ x. (x , b(x)) : A → Σ_{x : A} B(x)
--             is an equivalence.
--         (ii) The type B(x) is contractible for each x : A.
    postulate b : ∀ (x : A) → B x

    m : A → Σ[ x ∈ A ] B x
    m {A = A} {B = B} = λ x → (x , b {A = A} {B = B} x)

    -- observe that m̅ and pr₁ are extentionally the same
    -- so if m is equivalent, so is pr₁
    lem : is-equiv (m {A = A} {B = B}) → is-equiv (pr₁ {A = A} {B = B})
    lem {A = A} {B = B} ((m̅ , m∘m̅~id) , m̅' , m̅'∘m~id ) = (m , λ x → refl) , (m , ret )
      where
        m̅~pr₁ : m̅ ∼ pr₁
        m̅~pr₁ (x , y) =  ap pr₁ (m∘m̅~id (x , y))

        ret : (x : Σ A B) → m (pr₁ x) ≡ id x
        ret x = sym (ap (λ p → m p) (m̅~pr₁ x)) ○ (m∘m̅~id x)

    open PathReasoning
    -- let the previous exercise do the heavy lifting
    i⇒iic : is-equiv (m {A = A} {B = B}) → (x : A) → is-contr (B x)
    i⇒iic {A = A} {B = B} is-equiv-m x = (10-7b.i⇒ii ∘ lem) is-equiv-m x


    ii⇒ic : (any-is-contr : (x : A) → is-contr (B x)) → is-equiv (m {A = A} {B = B})
    ii⇒ic {A = A} {B = B} any-is-contr = (pr₁ , m∘pr₁∼id) , (pr₁ , pr₁∘m∼id)
      where
        center-B : (x : A) → (B x)
        center-B x = is-contr.center (any-is-contr x)

        contraction-B : (x : A) → (b : B x) → (center-B x ≡ b)
        contraction-B x = is-contr.contraction (any-is-contr x)

        m∘pr₁∼id : (m {A = A} {B = B} )∘ pr₁ ∼ id
        m∘pr₁∼id (a , ba) = ap (λ z → (a , z)) ((contraction-B a (b {B = B} (pr₁ {A = A} {B = B} (a , ba)))) ⁻¹ ○ contraction-B a ba )

        pr₁∘m∼id : pr₁ ∘ (m {A = A} {B = B}) ∼ id
        pr₁∘m∼id x = refl

-------------------------------------------------------------------------------
-- #10.8
--
-- Construct for any map f : A → B an equivalence e : A ≃ Σ_{y : B} (fib f y)
-- and a homotopy H : f ∼ pr₁ ∘ e witnessing that  the trianglke
--   {see text}
-- commutes. The projection pr₁ is sometimes also called the
-- *fibrant replacement* of f, because first projection maps are fibrations
-- in the homotopy interpretation of type theory.

module 10-8 where
  private
    variable
      ℓ : Level
      A B : Set ℓ
  -- We are given
  --   f : A → B.
  -- We want to first define
  --   e : A → Σ[ b ∈ B ] (fib f b).
  -- Then we want to prove that our e is an equivalence by defining
  --   e-is-equiv : A ≃ Σ[y ∈ B] fib f y.
  -- Lastly, we want to define
  --   H : f ∼ fst ∘ e
  -- With all these defined, we will return
  --   ((e , e-is-equiv) , H) : Σ[ (e , _) ∈ A ≃ (Σ[ b ∈ B ] (fib f b)) ] (f ∼ fst ∘ e)

  -- ERRATA: Rijke says e : A ≃ Σ[ y ∈ B ] fib f y, but then later writes "e" when he means "fst e".
  domain-≃-Σ-fib : (f : A → B) → Σ[ (e , _) ∈ A ≃ (Σ[ b ∈ B ] (fib f b)) ] (f ∼ fst ∘ e)
  domain-≃-Σ-fib {A = A} {B = B} f = (e , e-is-equiv) , H
    where
      -- To define e, we are given an a : A, and we want to produce
      -- an element b : B, an element a' : A, and a proof eq : f a' ≡ b.
      -- We let b ≔ f a, a' ≔ a, and eq ≔ refl:
      --   e a = f a , (a , refl).
      e : A → Σ[ b ∈ B ] (fib f b)
      e a = f a , (a , refl)

      -- e-sec-fun and e-retr-fun, both of type Σ[ b ∈ B ] (fib f b) → A, are easy to define.
      -- An element of fib f b is a pair consisting of an element a : A, and a proof that f a = b.
      -- So to define e-sec-fun and e-retr-fun, we simply return this a.
      e-is-equiv : is-equiv e
      e-is-equiv = e-sec , e-retr
        where
          e-sec-fun : Σ[ b ∈ B ] (fib f b) → A
          e-sec-fun (_ , (a , _)) = a

          -- To prove that e-sec-fun is a right inverse of e,
          -- we first assume we are given
          --   b : B,
          --   a : A,
          --   fa≡b : fa ≡ b.
          -- We must produce a proof that
          --   (e ∘ e-sec-fun (b , a , fa≡b)) ≡ id (b , a , fa≡b).
          -- Reducing this goal yields
          --   (f a , (a , refl)) ≡ (b , a , fa≡b).
          -- If only we had a way to turn b into f a, and to turn fa≡b into refl...
          e-sec-h : e ∘ e-sec-fun ∼ id
          e-sec-h (b , (a , fa≡b)) = ind≡ (f a) (λ b' fa≡b' → (e ∘ e-sec-fun) (b' , a , fa≡b') ≡ (b' , a , fa≡b')) refl b fa≡b
          -- Or we could have just pattern matched on _≡_:
          -- e-sec-h (b , (a , refl)) = refl

          e-sec : section e
          e-sec = e-sec-fun , e-sec-h

          -- The retraction turns out to be much easier, with the proof being refl.
          e-retr-fun : Σ[ b ∈ B ] (fib f b) → A
          e-retr-fun (_ , (a , _)) = a
          e-retr-h : e-retr-fun ∘ e ∼ id
          e-retr-h a = refl
          e-retr : retraction e
          e-retr = e-retr-fun , e-retr-h

      -- Finally, we prove commutativity, which is just refl-∼
      H : f ∼ fst ∘ e
      H = refl-∼


  -- To avoid patternInTele nonsense
  domain-≃-Σ-fib' : (f : A → B) → Σ[ e,_ ∈ A ≃ (Σ[ b ∈ B ] (fib f b)) ] (f ∼ fst ∘ (fst e,_))
  domain-≃-Σ-fib' = domain-≃-Σ-fib
