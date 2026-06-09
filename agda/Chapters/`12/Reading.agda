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
    A B : Set ℓ
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

  -- AH> Irrelevant types satisfy the UIP (defined in Prelude)
  -- Irrelevant⇒UIP : Irrelevant A → UIP A

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
  --  - Equiv⇒Embedding : (e : A ≃ B) → (is-emb (fst e))
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
      (λ a → Equiv⇒Embedding ((λ x → tt) , (10-3.const-tt-is-equiv (f a))))

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
propositionalEquivalence : {P Q : Set} → is-prop P → is-prop Q → ((P ≃ Q) ↔ (P ↔ Q))
propositionalEquivalence {P = P} {Q = Q} prop-p prop-q =
        (λ e → e .fst , e .snd .fst .fst)
        , λ { (f , g) → f ,
               has-inverse⇒is-equiv (g , (λ x → is-contr.center (prop-q (f (g x)) (id x))) ,
                                         (λ x → is-contr.center (prop-p (g (f x)) (id x))) ) }

--------------------------------------------------------------------
-- § 12.2 Subtypes

-- There is some correspondence between proposition on types and subsets in set theory

-- Definition 12.2.1
-- A type family B over A is said to be a subtype of A if for each x : A, B x is a proposition.
-- When B is a subtype of A, we also say that B x is a _property_ of x : A.
-- AH> For fun, see "Five stages of accepting constructive mathematics" by Andrej Baujer:
--     https://www.ams.org/journals/bull/2017-54-03/S0273-0979-2016-01556-4/S0273-0979-2016-01556-4.pdf
--     In particular, Theorem 2.1. Can you spot why we assert the property 𝐁 is a prop?
is-subtype : {A : Set} → (A → Set) → Set
is-subtype {A = A} 𝐁 = ∀ (x : A) → is-prop (𝐁 x)

-- Lemma 12.2.2
-- Let A B by types, let e : A ≃ B then we have
-- is-prop A ↔ is-prop B

-- A reusable, descriptively named version that implies Lemma 12.2.2.
-- The proof gist:
-- if f : A → B is an equivalence, its section f⁻¹ is an equivalence,
-- and therefore an embedding. In other words, (ap f⁻¹) is an equivalence.
-- Ex 10.3 states that if g : A → B is an equivalence and B is contractible,
-- then so is A. 
-- Hence we let 
--   A := x ≡ y
--   B := f⁻¹ x ≡ f⁻¹ y
--   g := (ap f⁻¹) : x ≡ y → f⁻¹ x ≡ f⁻¹ y.
-- to yield a goal
--    10-3.ex-10-3-ii-iii⇒i (ap f⁻¹) : 
--      is-Contr (f⁻¹ x ≡ f⁻¹ y) → is-equiv (ap f⁻¹) → is-contr (x ≡ y)
-- The first argument follows from A being a prop; the second follows
-- from f⁻¹ being an embedding.
-- 
≃-is-prop : ∀ {A B : Set ℓ} → (A ≃ B) → is-prop A → is-prop B
≃-is-prop eqv@(f , (f⁻¹ , sec) , retr) isProp x y  = 
  10-3.ex-10-3-ii-iii⇒i (ap f⁻¹) (isProp (f⁻¹ x) (f⁻¹ y)) (ap-equiv x y) 
  where
    f⁻¹-isEquiv : is-equiv f⁻¹
    f⁻¹-isEquiv = equivalence-inverse-equivalence ((f⁻¹ , sec) , retr)  
    
    f⁻¹-isEmbedding : is-emb f⁻¹ 
    f⁻¹-isEmbedding = Equiv⇒Embedding (f⁻¹ , f⁻¹-isEquiv) 
    open is-emb f⁻¹-isEmbedding

lem•12•2•2 : {A B : Set ℓ} → (A ≃ B) → is-prop A ↔ is-prop B
lem•12•2•2 {A = A} {B = B} eqv = ≃-is-prop eqv , ≃-is-prop (sym-≃ eqv)


-- Theorem 12.2.3
-- Consider a map f : A → B. The following are equivalent
-- (i) map f is an embedding
-- (ii) the fiber fib f b is a proposition for each b : B
module 12•2•3 {A B : Set ℓ} {f : A → B} where
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
--   (i) R(x, y) is a proposition for each x y
--  (ii) R is reflexive, as witnessed by ρ : Π_{x : A} R(x, x)
-- (iii) There is a map  R(x, y) → x ≡ y for each x and y
-- Then any family of maps
--        Π_{x y: A} x = y → R (x, y)
-- is a family of equivalences. Consequently, the type A is a set

module set-characterization {A : Set ℓ} {R : A → A → Set ℓ}
  (prop-R : ∀ (x y : A) → is-prop (R x y))
  (ρ : ∀ (x : A) → R x x)
  (f : ∀ (x y : A) → R x y → x ≡ y) where


  -- Define the family of maps as follows
  ind-eq : ∀ (x y : A) → (x ≡ y) → R x y
  ind-eq x y = g x (ρ x) y
    where
    g : (x : A) → R x x → ∀ (y : A) → (x ≡ y) → R x y
    g x rxx y refl = rxx

  -- Because R x y is a proposition -- forall r r' : R x y, is-contr (r ≡ r')
  -- We have that that R x y is a retract of x = y
  retract-f : ∀ x y → retraction (f x y)
  retract-f x y = (ind-eq x y) , (λ rxy → helper x y rxy )
    where
    open is-contr
    helper : ∀ x y → ∀ (rxy : R x y) → ind-eq x y (f x y rxy) ≡ id rxy
    helper x y rxy with f x y rxy
    ... | refl = is-contr.center (prop-R x y (ρ x) rxy)


  -- if f is a retraction, then tot f also is a retraction
  open PathReasoning
  retract-tot-f : ∀ x → retraction (tot (f x))
  retract-tot-f x =
    tot (ind-eq x) ,
    λ s → begin
      tot (ind-eq x) (tot (f x) s) ≡⟨ (11•8.part-b (f x) (ind-eq x) ⁻¹) s ⟩
      tot (λ y → ind-eq x y ∘ f x y) s ≡⟨ 11•8.part-a (λ y → ind-eq x y ∘ f x y) (λ x → id ∘ id)
                                          (λ x₁ x₂ → is-contr.center (prop-R x x₁ (ind-eq x x₁ (f x x₁ x₂)) x₂)) s ⟩
      s ∎

  is-contr-eq : ∀ x → is-contr (Σ[ y ∈ A ] (x ≡ y))
  is-contr-eq x = thm-10∙1∙4 x

  -- thus we can show that Σ[ y ∈ A ] R x y is contractible,
  -- because tot f is a retraction and Σ[ y ] x ≡ y is contractible for each x
  is-contr-R : ∀ (x : A) → is-contr (Σ[ y ∈ A ] R x y)
  is-contr-R x =  10-2.retract-is-contractible (tot (f x)) (retract-tot-f x) (is-contr-eq x)

  -- part A
  lem2 : (x y : A) → is-equiv (ind-eq x y)
  lem2 x = _↔_.from (11•2•2.i↔ii x (ρ x) (ind-eq x)) (is-contr-R x)

  -- we have that tot (f x) is a equivalence, as domain and codomain are contractible
  lem3 : (x : A) → is-equiv (tot (f x))
  lem3 x = 10-3.ex-10-3-i-ii⇒iii (tot (f x)) (is-contr-R x) (is-contr-eq x)

  -- hence f is a family of equivalences
  lem : ∀ (x : A) → ((y : A) → is-equiv (f x y))
  lem x y =  _↔_.to (11•1•3.thm (f x)) (lem3 x) y

  equiv : ∀ (x y : A) → (x ≡ y) ≃ (R x y)
  equiv x y = sym-≃ (f x y , lem x y)

  -- thus A is a set, by using lem•12•2•2 and f is a family of equivalences
  thm : is-set A
  thm x y = _↔_.from (lem•12•2•2 (equiv x y)) (prop-R x y)

-- Theorem 12.3.5
-- Any type with decidable equality is a set
has-decidable-equality⇒is-set : ∀ {A : Set} → has-decidable-equality A → is-set A
has-decidable-equality⇒is-set {A = A} d = set-characterization.thm {A = A} {R = R} R-is-prop R-refl R⇒identity
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

data 𝕋 : Set where
  -𝟚T : 𝕋
  succT : 𝕋 → 𝕋

-𝟙T : 𝕋
-𝟙T = succT -𝟚T

𝟘T :  𝕋
𝟘T = succT -𝟙T

nat-inj : ℕ → 𝕋
nat-inj zero = 𝟘T
nat-inj (suc n) = succT (nat-inj n)

-- Def 12.4.1

is-trunc : 𝕋 → Set ℓ → Set ℓ
is-trunc -𝟚T A = is-contr A
is-trunc (succT T) A = ∀ (x y : A) → is-trunc T (x ≡ y)

-- for any type A, we say that A is k-truncated, or a k-type
-- if there is a term of type is-trunc_k (A)
trunc-type : (ℓ : Level) → 𝕋 → Set (lsuc ℓ)
trunc-type ℓ k = Σ[ X ∈ Set ℓ ] is-trunc k X

-- A map f : A → B is k-truncated if its fibers are k-truncated
is-trunc-map : ∀ {A B : Set ℓ} → 𝕋 → (A → B) → Set ℓ 
is-trunc-map {B = B} k f = ∀ (b : B) → is-trunc k (fib f b)

-- Given a universe 𝓤, we define universe 𝓤≤k of k-truncated types by
--    𝓤≤k := Σ[x ∈ 𝓤] is-trunc k X
𝓤≤[_] : 𝕋 → (ℓ : Level) →  Set (lsuc ℓ)
𝓤≤[ k ] ℓ = Σ[ X ∈ Set ℓ ] is-trunc k X

-- Proposition 12.4.3
-- is A is a k-type, then A is also a k+1 type
k-type⇒k+1-type : (k : 𝕋) → (A : Set ℓ) → is-trunc k A → is-trunc (succT k) A
k-type⇒k+1-type -𝟚T A A-is-contr = is-contr⇒is-prop A A-is-contr
k-type⇒k+1-type (succT k) A A-is-k-trunc = λ x y → k-type⇒k+1-type _ _ (A-is-k-trunc x y)

-- Corollary 12.4.4
-- If A is a k-type then its identity types are also k-types
k-type⇒identity-k-types : (k : 𝕋) → (A : Set ℓ) → is-trunc k A → ∀ (x y : A) → is-trunc k (x ≡ y)
k-type⇒identity-k-types k A A-is-k-type = k-type⇒k+1-type k A A-is-k-type


-- Proposition 12.4.5
-- if e : A ≃ B is an equivalence, and B is a k-type then so is A
k-type-closed-under-equivalence : {A B : Set ℓ} → (k : 𝕋) (e : A ≃ B) → is-trunc k B → is-trunc k A
k-type-closed-under-equivalence -𝟚T (f , f-equiv) B-k-type = 10-3.ex-10-3-ii-iii⇒i f B-k-type f-equiv
k-type-closed-under-equivalence (succT k) (f , f-equiv) B-k-type = {!!}

-- Corollary 12.4.6: if f : A → B is an embedding, and B is a (k + 1)-type, then so is A.
k+1-domain : {A B : Set ℓ} (f : A → B) → is-emb f → (k : 𝕋) → 
             is-trunc (succT k) B → is-trunc (succT k) A
k+1-domain f isEmb k k+1-B x y = 
  k-type-closed-under-equivalence k (ap f , isEmb .is-emb.ap-equiv x y) (k+1-B (f x) (f y)) 

-- Theorem 12.4.7
-- Let f : A → B. The following are equivalent:
-- - (i) The map f is (k +1)-truncated
-- - (ii) For each x, y : A, the map (ap f) is k-truncated.

module _ {A B : Set ℓ} (f : A → B) (k : 𝕋) where
-- AH> I want to move onto Ch. 13
  postulate
    k+1-truncated⇒ap-k-truncated : 
      is-trunc-map (succT k) f → (x y : A) → is-trunc-map k (ap {x = x} {y} f)
