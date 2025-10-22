open import Rijke

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

-- Proven during seminar
axiom₂ : ∀ (m n : ℕ) → m ≡ n → distℕ m n ≡ distℕ n m
axiom₂ = {!!}

-- no thanks
axiom₃ : ∀ (m n k : ℕ) → distℕ m n ≲ (distℕ m k + distℕ n k)
axiom₃ = λ m n k → indℕ (λ x → distℕ m n ≲ (distℕ m x + distℕ n x)) {!!} {!!} k
