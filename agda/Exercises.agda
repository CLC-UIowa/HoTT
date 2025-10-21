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