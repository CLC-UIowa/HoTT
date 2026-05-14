module Chapters.`12.Reading where

open import Prelude
open import Chapters.`01-08.Exercises
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises


--------------------------------------------------------------------
-- Chapter 12: Propositions, sets and the higher truncation levels

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set
    𝐁 : A → Set

--------------------------------------------------------------------
-- § 12.1 Propositions

-- Def 12.1.1
-- A type A is a proposition if its identity types are contractible i.e

is-prop : ∀ {ℓ} → Set ℓ → Set ℓ
is-prop A = ∀ (x y : A) → is-contr (x ≡ y)

-- given a universe 𝓤, define Prop[𝓤] to be the type of all small propositions
-- AI> I can't make this work
-- AH> This is the closest Agda analogue
Prop[_] : (ℓ : Level) → Set (lsuc ℓ)
Prop[ ℓ ] = Σ[ X ∈ Set ℓ ] (is-prop X)



-- Example 12.1.2
-- Any contractible type is a proposition by Exercise 10.1
-- AH> Restating/proving here for easier reference and better naming than ex-10-1:
is-contr⇒is-prop : ∀ (A : Set ℓ) → is-contr A → is-prop A
is-contr⇒is-prop A (c , cntr) x y =
  (cntr x ⁻¹ ○ cntr y) , λ { refl → left-inv (cntr x) }


-- AH> I would really prefer we use Agda stdlib's ⊤ and ⊥ over 𝟙 and ∅,
--     and yes I am fully aware of the irony in asserting this simply
--     because 𝟙 does not render in my emacs font.
is-prop-⊥ : is-prop ⊥
is-prop-⊥ ()
is-prop-⊤ : is-prop ⊤
is-prop-⊤ = is-contr⇒is-prop ⊤ ⊤-contr

----------------------------------------
-- Proposition 12.1.3

-- Let A be a type, The following are equivalent
-- (i) Type A is a proposition
-- (ii) Any two terms of type A can be identified, i.e. there is a dependent function of type
--           is-prop′ A := Π_{x y : A} x ≡ y
-- (iii) The type A is contractible as soon as it is inhabited, i.e., there is a function of type
--           A → is-contr A
-- (iv) the map const_⋆ : A → ⊤ is an embedding

is-prop′ : Set ℓ → Set ℓ
is-prop′ A = ∀ (x y : A) → x ≡ y

module _ {A : Set} where
-- The proof proceeds by showing (i) → (ii) → (iii) → (iv) → i
  open is-contr

  -- AH> the simple intuition here is that if (x ≡ y) is contractible,
  --     it's inhabited! So we just take the center of contraction.
  is-prop⇒is-prop′ : is-prop A → is-prop′ A
  is-prop⇒is-prop′ isProp x y = isProp x y .center

  -- AH> Intuitively, is-prop′ says "all my elements are equal (but I may have
  --     none)" and is-contr says "I'm a prop AND I'm inhabited"; the proof is
  --     simply to let the inhabitant `a` be the center and let
  --       isProp a : ∀ (y : A) → a ≡ y
  --     be the contraction.
  is-prop′⇒contractibleIfInhabited : is-prop′ A → (A → is-contr A)
  is-prop′⇒contractibleIfInhabited isProp a = (a , isProp a)

  lemmer : {X Y : Set} → {f : X → Y} → (X → is-emb f) → is-emb f
  lemmer {f = f} m = Embed λ x y → m x .is-emb.ap-equiv x y

  -- Helpers:
  --  - thm•11•4•2 : (e : A ≃ B) → (is-emb (fst e))
  --  - const-tt-is-equiv : is-contr A → is-equiv {ℓ} {A} (const tt)
  -- AH> N.b. I prefer writing (λ (x : A) → tt) over (const tt), here,
  --     as we are making a statement about the type A (the domain).
  --
  --     The proof, in English:
  --     By the lemmer above, we have
  --       (A → is-emb (λ (x : A) → tt)) → is-emb (λ (x : A) → tt).
  --     This means we must show that
  --       GOAL: (A → is-emb (λ (x : A) → tt)),
  --     which is great! Importantly, this goal means we have an `a : A` in context.
  --     Theorem 11.4.2 says that if f is an equivalence, then f is an embedding. Applying yields:
  --       GOAL: A ≃ ⊤
  --     But we proved from exercise 10.3 (const-tt-is-equiv) that, if A is contractible, then
  --     (λ (x : A) → tt) is an equivalence. We have `a : A` in scope and `f : A → is-contr A`,
  --     hence
  --       (10-3.const-tt-is-equiv (f a) : is-equiv f
  --     which proves that A ≃ ⊤.
  contractibleIfInhabited→const⋆-embedding :
    (A → is-contr A) → is-emb (λ (x : A) → tt)
  contractibleIfInhabited→const⋆-embedding f =
    lemmer {f = λ (x : A) → tt}
      (λ a → thm•11•4•2 ((λ x → tt) , (10-3.const-tt-is-equiv (f a))))

  -- AH> An alternative route to proving (iv) to (i) is to use the below
  -- proof with a proof that is-prop′ implies is-prop...
  const⋆-embedding⇒is-prop′  : is-emb {A = A} (λ (x : A) → tt) → is-prop′ A
  const⋆-embedding⇒is-prop′ (Embed ap-equiv) x y = ap-equiv x y .fst .fst refl

  -- However this is not so simple...
  is-prop′⇒is-prop : is-prop′ A → is-prop A
  is-prop′⇒is-prop isProp x y = isProp x y , λ { refl → {!!} }

  const⋆-embedding⇒is-prop : is-emb {A = A} (λ (x : A) → tt) → is-prop A
  const⋆-embedding⇒is-prop (Embed ap-equiv) x y with ap-equiv x y
  ... | (f , sec) , retr = f refl ,
    λ { refl → {!sec refl!} }


-- Proposition 12.1.4
-- A map f : P → Q between to propositions P and Q is an equivalence
-- if and only if there is a map g : Q → P
prop•12•1•4 : {P Q : Set} → is-prop P → is-prop Q → ((P ≃ Q) ↔ (P ↔ Q))
prop•12•1•4 {P = P} {Q = Q} prop-p prop-q =
        (λ e → e .fst , e .snd .fst .fst)
        , λ { (f , g) → f ,
               has-inverse⇒is-equiv (g , (λ x → is-contr.center (prop-q (f (g x)) (id x))) ,
                                         (λ x → is-contr.center (prop-p (g (f x)) (id x))) ) }


--------------------------------------------------------------------
-- § 12.2 Subtypes

-- There is some correspondence between proposition on types and subsets in set theory

-- Definition 12.2.1
-- A type family B over A is said to be a subtype of A if for each x : A, B x is a proposition
-- When B is a subtype of A, we also say that B x is a _property_ of x : A
is-subtype : {A : Set} → (A → Set) → Set
is-subtype {A = A} 𝐁 = ∀ (x : A) → is-prop (𝐁 x)

-- Lemma 12.2.2
-- Let A B by types, let e : A ≃ B then we have
-- is-prop A ↔ is-prop B
lem•12•2•2 : (A ≃ B) → is-prop A ↔ is-prop B
lem•12•2•2 {A = A} {B = B} (f , is-equiv-f) = fwd , bwk  where
  fwd : is-prop A → is-prop B
  fwd prop-A x y = 10-3.ex-10-3-ii-iii⇒i (ap f̅) (prop-A (f̅ x) (f̅ y)) lem2
    where
      f̅ = is-equiv-f .fst .fst
      is-equiv-f̅ : is-equiv f̅
      is-equiv-f̅ = equivalence-inverse-equivalence is-equiv-f

      lem : is-contr-map (ap {x = x} {y = y} f̅)
      lem = thm•10•4•6 (ap {x = x} {y = y} f̅) (is-emb.ap-equiv (thm•11•4•2 (f̅ , is-equiv-f̅)) x y)

      lem2 : is-equiv (ap f̅)
      lem2 = is-contr-map-equiv lem


  bwk : is-prop B → is-prop A
  bwk prop-B x y = 10-3.ex-10-3-ii-iii⇒i (ap f) (prop-B (f x) (f y)) lem2  where
    lem : is-contr-map (ap f)
    lem = thm•10•4•6 (ap {x = x} {y = y} f) (is-emb.ap-equiv (thm•11•4•2 (f , is-equiv-f)) x y)

    lem2 : is-equiv (ap f)
    lem2 = is-contr-map-equiv lem



-- Theorem 12.2.3
-- Consider a map f : A → B. The following are equivalent
-- (i) map f is an embedding
-- (ii) the fiber fib f b is a proposition for each b : B
module 12•2•3 {f : A → B} where
  i→ii : is-emb f → ((b : B) → is-prop (fib f b))
  i→ii (Embed p) b (a , fa≡b) (a′ , fa′≡b) = {!!}



  ii→i : ((b : B) → is-prop (fib f b)) → is-emb f
  ii→i p = Embed (λ x y → {!p (f y) !})


-- Corollary 12.2.4: Consider a family B of types over A. The following are equivalent
-- (i) The map pr₁ : Σ_{x : A} B x → A is an embedding
-- (ii) The type B x is a proposition for each x : A


--------------------------------------------------------------------
-- § 12.3 Sets



--------------------------------------------------------------------
-- § 12.4 General truncation levels
