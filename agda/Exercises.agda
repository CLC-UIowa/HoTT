{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat.Properties

open import Rijke
open import Data.Nat.Properties

_≲_ : ℕ → ℕ → Set
_≲_ = λ m → indℕ (λ _ → ℕ → Set)
                 (λ n → indℕ (λ _ → Set)
                             𝟙
                             (λ n′ inner → 𝟙)
                             n)
                 (λ m′ outer n → indℕ (λ _ → Set)
                                      ∅
                                      (λ n′ inner → outer n′)
                                      n)
                 m

≲-refl : (m : ℕ) → m ≲ m
≲-refl = indℕ (λ m → m ≲ m) ⋆ (λ n → id)

≲anti-sym : (m n : ℕ) → m ≲ n → n ≲ m → m ≡ n
≲anti-sym = λ m → indℕ (λ m → ((n : ℕ) → m ≲ n → n ≲ m → m ≡ n))
                       (λ n → indℕ (λ n → (0 ≲ n → n ≲ 0 → 0 ≡ n)) (λ _ _ → refl) (λ m′ inner q₁ q₂ → ind∅ _ q₂) n)
                       (λ m′ outer n → indℕ (λ n → (suc m′ ≲ n → n ≲ suc m′ → suc m′ ≡ n))
                                            (λ q₁ q₂ → ind∅ _ q₁)
                                            (λ n′ inner q₁ q₂ → cong suc (outer n′ q₁ q₂))
                                            n)
                       m

--------------------------------------------------------------------------------
-- Exercise 6.5a: axioms of a metric

axiom₁ : ∀ (m n : ℕ) → m ≡ n → distℕ m n ≡ 0
axiom₁ = λ m n eq → ind≡ m (λ x _ → distℕ m x ≡ 0) (dist-lemma₃ m) n eq

-- thanks Andrew
suc-inj : (m n : ℕ) → suc m ≡ suc n → m ≡ n
suc-inj = λ m n x → ap pred′ (suc m) (suc n) x

-- Proven during seminar nope it sure as shit wasn't.
axiom₂ : ∀ (m n : ℕ) → m ≡ n → distℕ m n ≡ distℕ n m
axiom₂ = λ m → indℕ (λ m → (n : ℕ) → m ≡ n → distℕ m n ≡ distℕ n m)
                    (λ n → indℕ (λ n → 0 ≡ n → distℕ 0 n ≡ distℕ n 0) (λ z → refl) (λ n′ ih x → refl) n)
                    (λ m′ outer n → indℕ (λ n → suc m′ ≡ n → distℕ (suc m′) n ≡ distℕ n (suc m′))
                                         (λ z → refl)
                                         (λ n′ inner x → dist-lemma₂ m′ n′ □ (outer n′ (suc-inj m′ n′ x) □ sym (dist-lemma₂ n′ m′)))
                                         n)
                    m

-- no thanks
axiom₃ : ∀ (m n k : ℕ) → distℕ m n ≲ (distℕ m k + distℕ n k)
axiom₃ = λ m n k →
  indℕ (λ x → distℕ m n ≲ (distℕ m x + distℕ n x))
       (indℕ (λ m → distℕ m n ≲ (distℕ m 0 + distℕ n 0))
             (indℕ (λ n → distℕ 0 n ≲ (distℕ 0 0 + distℕ n 0))
                   ⋆
                   (λ n′ inner → ind≡ (suc n′) (λ d _ → d ≲ suc n′) (≲-refl (suc n′)) (distℕ 0 (suc n′)) (sym (dist-lemma₁′ (suc n′)))) n)
             {!   !}
             m)
       {!!}
       k
-------------------------------------------------------------------------------
-- Exercise 7.2

-- Show that the divisibility relation satisfies the laws of a poset

∣-refl : (n : ℕ) → n ∣ n
∣-refl = λ n → pair 1 (*-identityʳ n)

lem : ∀ m k k′ → suc m * (k * k′) ≡ suc m * 1 → k ≡ 1
lem m k k′ p = {!   !}

∣-antisym : (m n : ℕ) → m ∣ n → n ∣ m → m ≡ n
∣-antisym zero n (k , refl) (k′ , p′) = refl
∣-antisym (suc m) n (k , refl) (k′ , p′) = {!   !}


--------------------------------------------------------------------------------
-- #7.2
-- Show that the divisibility relation satisfies the axioms of a poset:
-- reflexive, antisymmetric, and transitive.

∣-reflexive : ∀ m → m ∣ m
∣-reflexive = λ m → pair 1 (*-identityʳ m)

lem : ∀ m k₁ k₂ → (suc m) * (k₁ * k₂) ≡ (suc m) * 1 → (k₁ ≡ 1)
lem = λ m k₁ k₂ eq → m*n≡1⇒m≡1 k₁ k₂ (*-cancelˡ-≡ (k₁ * k₂) 1 (suc m) eq)

∣-symmetric : ∀ m n → m ∣ n → n ∣ m → m ≡ n
∣-symmetric = λ m n m∣n n∣m →
  indΣ (λ v → m ≡ n)
  -- (tr {B = λ x → x * k′ ≡ m} _ _ (inv _ _ p) q)
  -- *-cancelˡ-≡ : (m₁ n₁ o : ℕ) .⦃ _ : NonZero o ⦄ → o * m₁ ≡ o * n₁ → m₁ ≡ n₁
  (λ k p → (indΣ (λ v → m ≡ n) (λ k′ q → {!(tr {B = λ x → x * k′ ≡ m} _ _ (inv _ _ p) q)  !}) n∣m)) m∣n
