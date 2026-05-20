module Chapters.`12.Reading where

open import Prelude
open import Chapters.`01-08.Exercises
open import Chapters.`01-08.Reading using (Eqℕ; toEqℕ; is-decidable; _⊎_; inr; inl; has-decidable-equality; ex-falso)
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


module _ where
  -- private variable
  --   A : Set ℓ
-- The proof proceeds by showing (i) → (ii) → (iii) → (iv) → i
  open is-contr

  -- AH> Rijke calls this is-prop′:
  --   is-prop′ : Set ℓ → Set ℓ
  --   is-prop′ A = ∀ (x y : A) → x ≡ y
  -- which sucks because it has a better, more descriptive name in the Prelude:
  -- Irrelevant : Set ℓ → Set ℓ
  -- Irrelevant A = ∀ (x y : A) → x ≡ y

  -- AH> I am going to deviate from the book here and prove directly that
  --       is-prop A ⇔ is-prop′ A.
  --     that is,
  --       is-prop A ⇔ Irrelevant A 
  --     We can then use this fact to complete the last step
  --     of Prop 12.1.3. The proof that is-prop and Irrelevant are equivalent
  --     follows from HoTT Book lemmas 3.3.4 and 3.11.10.
  --
  --     First I'm going to use the HoTT book def'n of is-set, which deviates from Rijke's.
  --     A "set", discussed later in ch. 12, is a type for which all proofs of
  --     equality are equal. In other words, they're sets for which the UIP holds.
  --     To avoid confusion, I'll call a spade a spade, and simply name this the UIP,
  --     which is defined in the prelude.    
  --       UIP : Set ℓ → Set ℓ
  --       UIP A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

  -- (i → ii)
  -- AH> the simple intuition here is that if (x ≡ y) is contractible,
  --     it's inhabited! So we just take the center of contraction.
  is-prop⇒Irrelevant : is-prop A → Irrelevant A
  is-prop⇒Irrelevant isProp x y = isProp x y .center

  -- AH> The reverse direction is more complicated. To make matters harder,
  -- let's prove a more important lemma: that if A is a mere prop, then
  -- A is also a set.
  -- The proof is some HoTT nonsense that goes like this:
  -- Define g(y) as "post-composing" y with x.
  -- Then prove that any proof of a ≡ b is equal to (g a) ⁻¹ ○ (g b);
  -- it follows now that
  --   - lem x y p : p = (g x) ⁻¹ ○ (g y)
  --   - lem x y q : q = (g x) ⁻¹ ○ (g y)
  Irrelevant⇒UIP : Irrelevant A → UIP A
  Irrelevant⇒UIP {A = A} isProp x y p q = lem x y p ○ (lem x y q) ⁻¹
      where
      g : (z : A) → x ≡ z
      g z = isProp x z

      lem : ∀ (a b : A) (p : a ≡ b) → p ≡ (g a) ⁻¹ ○ g b
      lem a b refl = (left-inv (g a)) ⁻¹

  -- This direction now falls out easily
  Irrelevant⇒is-prop : Irrelevant A → is-prop A
  Irrelevant⇒is-prop isProp x y =
    isProp x y , λ { q → Irrelevant⇒UIP isProp x y (isProp x y) q }

  -- (ii → iii)
  -- AH> Intuitively, Irrelevant says "all my elements are equal (but I may have
  --     none)" and is-contr says "I'm a prop AND I'm inhabited"; the proof is
  --     simply to let the inhabitant `a` be the center and let
  --       isProp a : ∀ (y : A) → a ≡ y
  --     be the contraction.
  Irrelevant⇒contractibleIfInhabited : Irrelevant A → (A → is-contr A)
  Irrelevant⇒contractibleIfInhabited isProp a = (a , isProp a)


  -- This is a simple trick that will "give us" an X in the next proof step.
  lemmer : {X Y : Set} → {f : X → Y} → (X → is-emb f) → is-emb f
  lemmer {f = f} m = Embed λ x y → m x .is-emb.ap-equiv x y

  -- (iii → iv)
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
  contractibleIfInhabited→const⋆-embedding {A = A} f =
    lemmer {f = λ (x : A) → tt}
      (λ a → thm•11•4•2 ((λ x → tt) , (10-3.const-tt-is-equiv (f a))))

  -- (iv → i)
  -- AH> Here we deviate from Rijke. It's *much simpler* to prove that,
  --     if (λ (x : A) → tt) is an embedding, that all x, y : A are equal.
  const⋆-embedding⇒Irrelevant  : is-emb {A = A} (λ (x : A) → tt) → Irrelevant A
  const⋆-embedding⇒Irrelevant (Embed ap-equiv) x y = ap-equiv x y .fst .fst refl

  -- AH> Now use the implication from Irrelevant A to is-prop A to complete the proof.
  const⋆-embedding⇒is-prop : is-emb {A = A} (λ (x : A) → tt) → is-prop A
  const⋆-embedding⇒is-prop emb = Irrelevant⇒is-prop (const⋆-embedding⇒Irrelevant emb)


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
lem•12•2•2 : {A B : Set ℓ} → (A ≃ B) → is-prop A ↔ is-prop B
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
  i→ii (Embed p) b (a , fa≡b) (a′ , fa′≡b) = _↔_.to (lem•12•2•2 (lem2 a b fa≡b)) ({!!}  ) (a , fa≡b) (a′ , fa′≡b)
    where
      fwd : is-emb f → (∀ x → is-contr (Σ[ y ∈ A ] (f x ≡ f y)))
      fwd ef x = {!10-3.ex-10-3-i-iii⇒ii (ap f) ? ?  !}

      bwk : (∀ x → is-contr (Σ[ y ∈ A ] (f x ≡ f y))) → is-emb f
      bwk ctr = Embed (λ x y → 10-3.ex-10-3-i-ii⇒iii (ap f) {!!} {!!})


      lem : is-emb f ↔ (∀ x → is-contr (Σ[ y ∈ A ] (f x ≡ f y)))
      lem = fwd , bwk

      lem2 : ∀ y b → (e : f y ≡ b) → fib f (f y) ≃ fib f b
      lem2 y b refl = id , (id , (λ x → refl)) , id , (λ x → refl)


  ii→i : ((b : B) → is-prop (fib f b)) → is-emb f
  ii→i p = Embed (λ x y → 10-3.ex-10-3-i-ii⇒iii (ap f) {!!} {! p (f y)!})


-- Corollary 12.2.4: Consider a family B of types over A. The following are equivalent
-- (i) The map pr₁ : Σ_{x : A} B x → A is an embedding
-- (ii) The type B x is a proposition for each x : A


--------------------------------------------------------------------
-- § 12.3 Sets

-- Definition 12.3.1
-- A type A is said to be a *set* if its identity types are propositions
is-set : Set ℓ → Set ℓ
is-set A = ∀ (x y : A) → is-prop (x ≡ y)

-- Example 12.3.2
-- The type of natural numbers is a set
is-set-ℕ : is-set ℕ
is-set-ℕ = λ x y →  _↔_.from (lem•12•2•2 (toEqℕ x y , 11•3•1.thm x y)) (lem x y)
  where
    lem : (x y : ℕ) → is-prop (Eqℕ x y)
    lem zero zero Chapters.`01-08.Reading.⋆ Chapters.`01-08.Reading.⋆ = refl , (λ { refl → refl })
    lem zero (suc y) () e2
    lem (suc x) zero e1 ()
    lem (suc x) (suc y) e1 e2 = lem x y e1 e2

-- Proposition 12.3.3
-- Consider a type A. The following are equivalent
-- (i) A type A is a set
-- (ii) The type A satisfies axiom K i.e. if and only if its comes equipped with a term of type
--      axiom-K (A) := Π_{x : A} Π_{p : x = x} refl_x = p
axiom-K : Set ℓ → Set ℓ
axiom-K A = ∀ (x : A) → ∀ (p : x ≡ x) → refl {x = x} ≡ p

module _ where
  set⇒axiom-K : is-set A → axiom-K A
  set⇒axiom-K = λ z x p → is-contr.center (z x x refl p)

  axiom-K⇒set : axiom-K A → is-set A
  axiom-K⇒set axiomK x y p q = Irrelevant⇒is-prop lem p q
    where
      open PathReasoning
      lem : ∀ (p q : x ≡ y) → p ≡ q
      lem p q = sym (begin q  ≡⟨ (right-identity {{PathGroupoid}} _) ⁻¹ ⟩
                       q ○ refl ≡⟨ (q ⋆ᵣ axiomK y (q ⁻¹ ○ p)) ⟩
                       q ○ (q ⁻¹ ○ p) ≡⟨ sym (assoc q (q ⁻¹) p) ⟩
                       (q ○ q ⁻¹) ○ p ≡⟨ (right-inv q) ⋆ₗ p ⟩
                       refl ○ p ≡⟨ left-identity {{PathGroupoid}} _ ⟩
                       p  ∎)

-- Theorem 12.3.4
-- Let A be a type, and let R : A → A → 𝓤 be a binary relation on A satisfying
-- (i) Each R(x, y) is a proposition
-- (ii) R is reflexive, as witnessed by ρ : Π_{x : A} R(x, x)
-- (iii) There is a map  R(x, y) → x ≡ y for each x and y
-- Then any family of maps
--        Π_{x y: A} x = y → R (x, y)
-- is a family of equivalences. Consequently, the type A is a set

module 12•3•4 {A : Set ℓ} {R : A → A → Set ℓ}
  (prop-R : ∀ (x y : A) → is-prop (R x y))
  (ρ : ∀ (x : A) → R x x)
  (f : ∀ (x y : A) → R x y → x ≡ y) where

  ind-eq : (x : A) → R x x → ∀ (y : A) → (x ≡ y) → R x y
  ind-eq x = {!!}

  lem : ∀ (x y : A) → is-equiv (f x y)
  lem x y = {!tot (f x)!}

  equiv : ∀ (x y : A) → (x ≡ y) ≃ (R x y)
  equiv x y = sym-≃ (f x y , lem x y)

  thm : is-set A
  thm x y = _↔_.from (lem•12•2•2 (equiv x y)) (prop-R x y)

-- Theorem 12.3.5
-- Any type with decidable equality is a set
has-decidable-equality⇒is-set : ∀ {A : Set} → has-decidable-equality A → is-set A
has-decidable-equality⇒is-set {A = A} d = 12•3•4.thm {A = A} {R = R} R-is-prop R-refl R⇒identity
  where
    R' : ∀ (x y : A) → is-decidable (x ≡ y) → Set
    R' x y (inl p) = ⊤
    R' x y (inr p) = ⊥

    R'-is-prop : ∀ (x y : A) → ∀ (q : is-decidable (x ≡ y)) → is-prop (R' x y q)
    R'-is-prop x y (inl x₁) = is-prop-⊤
    R'-is-prop x y (inr x₁) = is-prop-⊥

    R : ∀ (x y : A) → Set
    R x y = R' x y (d x y)

    R-is-prop : ∀ (x y : A) → is-prop (R x y)
    R-is-prop x y with d x y
    ... | inl p = λ { tt tt → refl , (λ { refl → refl }) }
    ... | inr p = λ { () y }

    R-refl : ∀ x → R x x
    R-refl x with d x x
    ... | inl x₁ = tt
    ... | inr p = p refl

    f : ∀ x y → (q : is-decidable (x ≡ y)) → R' x y q → x ≡ y
    f x y (inl p) = λ r → p
    f x y (inr p) = λ r → ex-falso r

    R⇒identity : (x y : A) → R x y → x ≡ y
    R⇒identity x y r with d x y
    ... | inl p = p

--------------------------------------------------------------------
-- § 12.4 General truncation levels
