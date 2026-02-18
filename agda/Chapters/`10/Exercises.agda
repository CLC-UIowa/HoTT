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
      center-x≡y = (! C x) ○ C y

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

  const-tt-has-section :  is-contr A → section {ℓ} {A} (const tt)
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

  const-tt-has-retraction : is-contr A → retraction {ℓ} {A} (const tt)
  const-tt-has-retraction (center , contraction) = const center , contraction

  {-
  -- We have all we need to show that (const tt) is an equivalence from A to ⊤.
  -}

  const-tt-is-equiv : is-contr A → is-equiv {ℓ} {A} (const tt)
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

  A-is-contractible : is-equiv {ℓ} {A} (const tt) → is-contr A
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

  ex-10-3-i-ii⇒iii : (f : A → B) →  is-contr A → is-contr B → is-equiv f
  ex-10-3-i-ii⇒iii {A = A} {B = B} f (a , prf-cA) (b , prf-cB)  = f-sec , f-retr
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
                  (const tt , refl-htpy _)

      f-sec : section f
      f-sec = g-sec→f-sec  (const tt , prf-cB)

      f-retr : retraction f
      f-retr =  h-ret→f-ret (snd is-equiv-const-tt-A)

  lem : {A B : Set ℓ} → (f : A → B) → (eq-f : is-equiv f) → retraction (`sec eq-f)
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

  ex-10-3-i-iii⇒ii : {A B : Set ℓ}(f : A → B) →  is-contr A → is-equiv f → is-contr B
  ex-10-3-i-iii⇒ii {A = A} {B = B} f ctr-A eq-f = 10-2.retract-is-contractible (`sec eq-f) (lem f eq-f) ctr-A

  {-
  -- A is a retract of B because f : A → B is an equivalence and therefore has a
  -- retraction.
  -- We're given that B is contractible.
  -- Use exercise 10.2 to conclude that A is contractible.
  -}

  ex-10-3-ii-iii⇒i : {A B : Set ℓ}(f : A → B) →  is-contr B → is-equiv f → is-contr A
  ex-10-3-ii-iii⇒i {A = A} {B = B} f ctr-B eq-f = 10-2.retract-is-contractible f (snd eq-f) ctr-B
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
      bad = ! (contraction fzero) ○ ((contraction (fsuc fzero)))


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
      cA ≡⟨ ap fst (! lem ○ contrAB (a , cB)) ⟩
      a ∎

    contr-B : is-contr B
    contr-B = cB , λ b → begin
      cB ≡⟨ ap snd  ( ! lem ○ contrAB (cA , b)) ⟩
      b ∎

-----------------------------------------------------------------------------

module 10-6 where
  private
    variable
      ℓ : Level
      A : Set ℓ
      B : A → Set ℓ
  open PathReasoning
  open import Agda.Builtin.Sigma

  f : (a : A) → B a → (Σ[ x ∈ A ] (B x))
  f a y = (a , y) 

  f-retr : (A-is-contr : is-contr A) → retraction {A = B (is-contr.center A-is-contr)} {B = Σ[ x ∈ A ] (B x) } (f (is-contr.center A-is-contr)) 
  f-retr {A = A} {B = B} A-is-contr = (λ{ (x , p) → tr B ((! (C' x))) p}) , λ (y : (B a)) → begin 
    ((λ { (x , p) → tr B (! C' x) p }) (f (is-contr.center A-is-contr) y)) ≡⟨ refl ⟩ 
    ((λ { (x , p) → tr B (! C' x) p }) (a , y)) ≡⟨ refl ⟩
    (tr B (! C' a) y) ≡⟨ ap (λ (h : a ≡ a) → tr B (! h) y) p ⟩ 
    (tr B (! refl) y) ≡⟨ refl ⟩
    (tr B refl y) ≡⟨ refl ⟩
    y ≡⟨ refl ⟩  
    id y ∎
    where 
      a : A 
      a = is-contr.center A-is-contr
      C : (x : A) → a ≡ x
      C = is-contr.contraction A-is-contr
      C' : (x : A) → a ≡ x 
      C' x = (! (C a)) ○ C x
      p : C' a ≡ refl
      p = left-inv (C a)

  f-section : (A-is-contr : is-contr A) → section {A = B (is-contr.center A-is-contr)} {B = Σ[ x ∈ A ] (B x) } (f (is-contr.center A-is-contr)) 
  f-section {A = A} {B = B} A-is-contr = (λ{ (x , p) → tr B ((! (C' x))) p}) , λ (x : Σ[ x ∈ A ] (B x)) → begin
    f (is-contr.center A-is-contr) ((λ { (x , p) → tr B (! C' x) p }) x) ≡⟨ refl ⟩
    f a ((λ { (x , p) → tr B (! C' x) p }) x) ≡⟨ refl ⟩
    f a (tr B (! C' (fst x)) (snd x)) ≡⟨ {!   !} ⟩
    -- (a , (tr B (! C' (fst x)) (snd x))) ≡⟨ ap (λ (h : A) → (h , (tr B (! (C' (fst x))) (snd x)))) (C' (fst x)) ⟩ 
    -- (a , (tr B (! C' a) (snd x))) ≡⟨ ? ⟩ 
    -- ((fst x) , (tr B (! C' (fst x)) (snd x))) ≡⟨ ? ⟩ 
    id x ∎ 
    
    where
      a : A 
      a = is-contr.center A-is-contr
      C : (x : A) → a ≡ x
      C = is-contr.contraction A-is-contr
      C' : (x : A) → a ≡ x 
      C' x = (! (C a)) ○ C x
      p : C' a ≡ refl
      p = left-inv (C a)



-------------------------------------------------------------------------------

-- #10.7

module 10-7 where
  module 10-7a where
    f : {ℓ : Level} → {A : Set ℓ} → {B : A → Set ℓ} → (a : A) → fib fst a → B a
    f {_} {A} {B} a ((x , y), p) = tr B p y

    is-equiv-f : {ℓ : Level} → {A : Set ℓ} → {B : A → Set ℓ} → (a : A) →
                 is-equiv (f {ℓ} {A} {B} a)
    is-equiv-f {ℓ} {A} {B} a = section-f , retraction-f
      where
        inv-f : (a : A) → B a → fib fst a
        inv-f a y = ((a , y) , refl)

        section-f : section (f a)
        section-f = (inv-f a) , refl-htpy id

        infix 4 _≡f_
        _≡f_ : fib fst a → fib fst a → Set ℓ
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
      
