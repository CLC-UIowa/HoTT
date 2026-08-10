module Chapters.`01-08.Exercises where 

import Data.Empty
open import Prelude using (_↔_)
open import Data.Nat hiding (_!; _<_ ; _⊔_)
open import Data.Product
import Data.Unit
open import Function hiding (_↔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (J)
open import Level using (Level)
open import Agda.Primitive using (lsuc ; _⊔_ ; Setω)
open import Data.Nat.Properties
open import Chapters.`01-08.Reading renaming (𝟙 to ⊤ ; ind𝟙 to ind⊤)

_≲_ : ℕ → ℕ → Set
_≲_ = λ m → indℕ (λ _ → ℕ → Set)
                 (λ n → indℕ (λ _ → Set)
                             ⊤
                             (λ n′ inner → ⊤)
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

--------------------------------------------------------------------------------
-- #7.2
-- Show that the divisibility relation satisfies the axioms of a poset:
-- reflexive, antisymmetric, and transitive.

∣-reflexive : ∀ m → m ∣ m
∣-reflexive = λ m → pair 1 (*-identityʳ m)

lem-suc* : ∀ m k₁ k₂ → (suc m) * (k₁ * k₂) ≡ (suc m) * 1 → (k₁ ≡ 1)
lem-suc* = λ m k₁ k₂ eq → m*n≡1⇒m≡1 k₁ k₂ (*-cancelˡ-≡ (k₁ * k₂) 1 (suc m) eq)

∣-antisym′ : ∀ m n → m ∣ n → n ∣ m → m ≡ n
∣-antisym′ zero n (k , refl) (k′ , q′) = refl
∣-antisym′ (suc m) n (k , refl) (k′ , q′)
  rewrite m*n≡1⇒m≡1 k k′
            (*-cancelˡ-≡ (k * k′) 1 (suc m)
              ((sym (*-assoc (suc m) k k′) □ q′) □ sym (*-identityʳ (suc m))))
  = sym (*-identityʳ (suc m))

∣-antisym : ∀ m n → m ∣ n → n ∣ m → m ≡ n
∣-antisym m n m∣n n∣m =
  -- Try using this as starting point:
  -- indℕ ? ? ? m ...
  indΣ (λ v → m ≡ n)
  -- (tr {B = λ x → x * k′ ≡ m} _ _ (inv _ _ p) q)
  -- *-cancelˡ-≡ : (m₁ n₁ o : ℕ) .⦃ _ : NonZero o ⦄ → o * m₁ ≡ o * n₁ → m₁ ≡ n₁
  (λ k p → (indΣ (λ v → m ≡ n) (λ k′ q → {!(tr {B = λ x → x * k′ ≡ m} _ _ (inv _ _ p) q)  !}) n∣m)) m∣n

∣-transitive′ : ∀ m n p → m ∣ n → n ∣ p → m ∣ p
∣-transitive′ m n p (x , refl) (y , refl) = (x * y) , sym (*-assoc m x y)

-- indΣ : ∀ {A : Set} {B : A → Set} → (P : Σ A B → Set ℓ) → ((x : A) → (y : B x) → P (pair x y)) → (z : Σ A B) → P z
∣-transitive : ∀ m n p → m ∣ n → n ∣ p → m ∣ p
∣-transitive m n p m|n = indΣ (λ _ → n ∣ p → m ∣ p)
                 (λ x e → ind≡ (m * x)
                   (λ n' _ → n' ∣ p → m ∣ p)
                   (λ n'|p → indΣ (λ _ → m ∣ p) (λ y e' →
                      ind≡ (m * x * y) (λ p' _ → m ∣ p') (x * y , sym (*-assoc m x y)) p e') n'|p) n e)
                 m|n


-- Exercise 7.7

import Data.Unit as Unit
⊤-η-law : ∀ (p : Unit.⊤) → p ≡ Unit.tt
⊤-η-law p = refl

-- classical-Fin : ℕ → Set
-- classical-Fin = λ k → Σ[ x ∈ ℕ ] x < k
<-irr-cheat : (a b : ℕ) → (p q : a < b) -> p ≡ q
<-irr-cheat zero (suc b) ⋆ ⋆ = refl
<-irr-cheat (suc n) (suc m) p q = <-irr-cheat n m p q

<-irr : (a b : ℕ) → (p q : a < b) → p ≡ q
<-irr a = indℕ (λ a → (b : ℕ) → (p q : a < b) → p ≡ q)
      {- pa ₀ -} (λ b → indℕ (λ b → (p q : 0 < b) → p ≡ q)
               {-pb 0 -} (λ p → ex-falso p)
               {-pb s -} (λ n ih p →
                           ind⊤ (λ (p : 0 < suc n) → (q : 0 < suc n) → p ≡ q)
                                (ind⊤ (λ q → ⋆ ≡ q) refl)
                                p)
                        b)
      {- pa ₛ -} (λ n iha b → indℕ ((λ b → (p q : suc n < b) → p ≡ q))
                    {-pb 0-}(λ p → ex-falso p)
                    {-pb 1-}(λ m ihb → iha m)
                    b)
               a
-- Part (a)
ex77alr : (k : ℕ) → (x y : classical-Fin k)
        → (x ≡ y) → pr₁ x ≡ pr₁ y
ex77alr k x y p = ap pr₁ x y p

ex77arl-cheat : (k : ℕ) → (x y : classical-Fin k)
        → pr₁ x ≡ pr₁ y → (x ≡ y)
ex77arl-cheat k (n , n<k) (m , n<k') refl = ap (_,_ n) n<k n<k' (<-irr n k n<k n<k')


ex77arl : (k : ℕ) → (x y : classical-Fin k)
        → pr₁ x ≡ pr₁ y → (x ≡ y)
ex77arl k  = λ x y → 
  indΣ 
    (λ x → pr₁ x ≡ pr₁ y → x ≡ y) 
    (λ a a<k → indΣ 
       (λ y → a ≡ pr₁ y → pair a a<k ≡ y) 
       (λ b b<k → 
          λ eq → ind≡ 
            a 
            -- Using Andrew's Cedille generalization trick to bring e : b ≡ n
            -- into scope is crucial here.
            (λ n a≡n → (e : b ≡ n) → pair a a<k ≡ pair n (tr _ _ e b<k)) 
            (λ e → ap (pair a) a<k (tr _ _ e b<k) (<-irr a k a<k (tr b a e b<k))) 
            b eq  refl) 
       y)
    x
