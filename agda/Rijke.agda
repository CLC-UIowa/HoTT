{-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Rijke where

import Data.Empty
open import Data.Nat hiding (_!; _<_) public
open import Data.Product public
import Data.Unit
open import Function public
open import Relation.Binary
open import Relation.Binary.PropositionalEquality public

open import Level using (Level)

variable
  ℓ : Level
  A B : Set

-------------------------------------------------------------------------------
-- Section 1.3: Natural numbers

indℕ : (P : ℕ → Set ℓ) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ _ pz ps 0 = pz
indℕ P pz ps (suc m) = ps m (indℕ P pz ps m)

add′ : ℕ → ℕ → ℕ
add′ zero n = n
add′ (suc m′) n = suc (add′ m′ n)

add : ℕ → ℕ → ℕ
add = λ m n → indℕ (λ _ → ℕ)
                   n
                   (λ m′ m′+n → suc m′+n)
                   m

_ : add 1 2 ≡ 3
_ = refl

pred′ : ℕ → ℕ
pred′ = λ m → indℕ (λ _ → ℕ) 0 (λ m′ _ → m′) m

_ : pred′ 4 ≡ 3
_ = refl


-------------------------------------------------------------------------------
-- Section 1.4.2 The unit type
--

-- To align with Rijke's notation:

data 𝟙 : Set where
  ⋆ : 𝟙

ind𝟙 : (P : 𝟙 → Set ℓ) → P ⋆ → (u : 𝟙) → P u
ind𝟙 P p⋆ ⋆ = p⋆

-------------------------------------------------------------------------------
-- Section 1.4.3 The empty type

∅ : Set
∅ = Data.Empty.⊥

ind∅ : (P : ∅ → Set ℓ) → (x : ∅) → P x
ind∅ _ ()

ex-falso : ∅ → A
ex-falso {A} = ind∅ (λ _ → A)

¬_ : Set → Set
¬ A = A → ∅

-- Proposition 4.3.4

contrapositive : (A → B) → (¬ B → ¬ A)
contrapositive = λ A→B B→∅ A → B→∅ (A→B A)

-------------------------------------------------------------------------------
-- Section 1.4.4 Coproducts

-- To avoid overloading `+`, we stick with Agda's `⊎` for coproducts...

data _⊎_ (A : Set) (B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

ind⊎ : (P : A ⊎ B → Set ℓ) → ((x : A) → P (inl x)) → ((y : B) → P (inr y)) → (z : A ⊎ B) → P z
ind⊎ _ onl _ (inl x) = onl x
ind⊎ _ _ onr (inr y) = onr y

-- Proposition 4.4.3

∅-lunit-⊎ : ¬ A → A ⊎ B → B
∅-lunit-⊎ {A} {B} ¬A = ind⊎ (λ _ → B) (ex-falso ∘ ¬A) id

-------------------------------------------------------------------------------
-- Section 1.4.5 Integers

-- Can't be arsed.

-------------------------------------------------------------------------------
-- Section 1.4.6 Dependent pairs

pair : ∀ {A : Set} {B : A → Set} → (x : A) → B x → Σ A B
pair = λ x y → x , y

indΣ : ∀ {A : Set} {B : A → Set} → (P : Σ A B → Set ℓ) → ((x : A) → (y : B x) → P (pair x y)) → (z : Σ A B) → P z
indΣ P f (x , y) = f x y

-- Definition 4.6.2

pr₁ : ∀ {A : Set} {B : A → Set} → Σ A B → A
pr₁ {A} {B} = indΣ (λ _ → A) (λ x y → x)

pr₂ : ∀ {A : Set} {B : A → Set} → (z : Σ A B) → B (pr₁ z)
pr₂ {A} {B} = indΣ (λ z → B (pr₁ z)) (λ x y → y)

-------------------------------------------------------------------------------
-- Section 1.5 Identity types

-- We use `refl` unchanged

ind≡ : (a : A) → (P : (x : A) → a ≡ x → Set ℓ) → P a refl → (x : A) → (p : a ≡ x) → P x p
ind≡ _ _ p _ refl = p

concat : (x y z : A) → x ≡ y → y ≡ z → x ≡ z
concat = λ x y z p → ind≡ x (λ y x≡y → y ≡ z → x ≡ z) id y p

_□_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p □ q = concat _ _ _ p q

inv : (x y : A) → x ≡ y → y ≡ x
inv = λ x y p → ind≡ x (λ y x≡y → y ≡ x) refl y p

assoc-lemma : (x y : A) (p : x ≡ y) (z : A) (q : y ≡ z) (w : A) (r : z ≡ w) → (p □ q) □ r ≡ p □ (q □ r)
assoc-lemma {A} = λ x y p → ind≡ x (λ y x≡y → (z : A) (q : y ≡ z) (w : A) (r : z ≡ w) → (x≡y □ q) □ r ≡ x≡y □ (q □ r))
                                   (λ _ _ _ _ → refl)
                                   y
                                   p

assoc : (x y z w : A) → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (p □ q) □ r ≡ p □ (q □ r)
assoc = λ x y z w p q r → assoc-lemma x y p z q w r

left-inv : (x y : A) (p : x ≡ y) → inv x y p □ p ≡ refl
left-inv = λ x y p → ind≡ x (λ y x≡y → inv x y x≡y □ x≡y ≡ refl) refl y p

ap : (f : A → B) (x y : A) → x ≡ y → f x ≡ f y
ap = λ f x y p → ind≡ x (λ y x≡y → f x ≡ f y) refl y p

ap-id : (x y : A) (p : x ≡ y) → p ≡ ap id x y p
ap-id = λ x y p → ind≡ x (λ y x≡y → x≡y ≡ ap id x y x≡y) refl y p

tr : {A : Set} {B : A → Set} (x y : A) → x ≡ y → B x → B y
tr {A} {B} = λ x y p → ind≡ x (λ y x≡y → B x → B y) id y p

apd : {A : Set} {B : A → Set} (f : (x : A) → B x) (x y : A) (p : x ≡ y) → tr x y p (f x) ≡ f y
apd = λ f x y p → ind≡ x (λ y x≡y → tr x y x≡y (f x) ≡ f y) refl y p

-------------------------------------------------------------------------------
-- Section 1.6 Universes

-- Most of this development is already in Agda, via `Set`.

Eqℕ : ℕ → ℕ → Set
Eqℕ = λ m → indℕ (λ m → ℕ → Set)
                 (λ n → indℕ (λ n → Set) 𝟙 (λ n′ inner → ∅) n)
                 (λ m′ outer n → indℕ (λ n → Set) ∅ (λ n′ inner → outer n′) n)
                 m

-- Just to confirm that makes sense...

_ : Eqℕ 0 0 ≡ 𝟙
_ = refl

_ : Eqℕ 2 3 ≡ ∅
_ = refl

_ : Eqℕ 3 3 ≡ 𝟙
_ = refl

-- Lemma 6.3.2

refl-Eqℕ : (n : ℕ) → Eqℕ n n
refl-Eqℕ = λ n → indℕ (λ n′ → Eqℕ n′ n′) ⋆ (λ n′ ih → ih) n

-- Proposition 6.3.3

toEqℕ : (m n : ℕ) → m ≡ n → Eqℕ m n
toEqℕ = λ m n p → ind≡ m (λ n m≡n → Eqℕ m n) (indℕ (λ m → Eqℕ m m) ⋆ (λ m′ ih → ih) m) n p

fromEqℕ : (m n : ℕ) → Eqℕ m n → m ≡ n
fromEqℕ = λ m → indℕ (λ m → (n : ℕ) → Eqℕ m n → m ≡ n)
                     (λ n → indℕ (λ n → Eqℕ 0 n → 0 ≡ n) (λ _ → refl) (λ m ih → ex-falso) n)
                     (λ m′ outer n → indℕ (λ n → Eqℕ (suc m′) n → suc m′ ≡ n)
                                          ex-falso
                                          (λ n′ inner p → ap suc m′ n′ (outer n′ p))
                                          n)
                     m

-------------------------------------------------------------------------------
-- Section 1.7 Modular arithmetic

import Data.Nat.Properties as ℕ

_∣_ : ℕ → ℕ → Set
d ∣ n = Σ ℕ (λ k → d * k ≡ n)

-- Proposition 7.1.5

prop715 : (d x y : ℕ) → d ∣ x → d ∣ y → d ∣ (x + y)
prop715 = λ d x y d∣x d∣y →
  indΣ (λ _ → d ∣ (x + y))
       (λ k₁ q₁ → indΣ (λ _ → d ∣ (x + y))
                       (λ k₂ q₂ → pair (k₁ + k₂)
                                       (ℕ.*-distribˡ-+ d k₁ k₂ □ (ap (λ z → z + d * k₂) (d * k₁) x q₁ □ ap (λ z → x + z) (d * k₂) y q₂)))
                       d∣y)
       d∣x

distℕ : ℕ → ℕ → ℕ
distℕ = λ m → indℕ (λ m → ℕ → ℕ)
                   (λ n → indℕ (λ n → ℕ) 0 (λ _ _ → n) n)
                   (λ m′ ih n → indℕ (λ n → ℕ) (suc m′) (λ n′ _ → ih n′) n)
                   m

_ : distℕ 0 4 ≡ 4
_ = refl

_ : distℕ 2 2 ≡ 0
_ = refl

--------------------------------------------------------------------------------
-- dist-lemmas


dist-lemma₁ : (n : ℕ) → distℕ n 0 ≡ n
dist-lemma₁ = indℕ (λ n → distℕ n 0 ≡ n) refl (λ _ _ → refl)

dist-lemma₁′ : (n : ℕ) → distℕ 0 n ≡ n
dist-lemma₁′ = λ n → indℕ (λ n → distℕ 0 n ≡ n) refl (λ n z → refl) n


dist-lemma₂ : (m n : ℕ) → distℕ (suc m) (suc n) ≡ distℕ m n
dist-lemma₂ = indℕ (λ m → (n : ℕ) → distℕ (suc m) (suc n) ≡ distℕ m n)
                   (λ n → refl)
                   (λ m′ outer n → indℕ (λ n → distℕ (suc (suc m′)) (suc n) ≡ distℕ (suc m′) n)
                                        refl
                                        (λ n′ inner → outer n′)
                                        n)

dist-lemma₃ : (n : ℕ) → distℕ n n ≡ 0
dist-lemma₃ = indℕ (λ n → distℕ n n ≡ 0) refl (λ n ih → dist-lemma₂ n n □ ih)


--------------------------------------------------------------------------------
-- §7 modular arithmetic

_≅_mod_ : ℕ → ℕ → ℕ → Set
x ≅ y mod k = k ∣ distℕ x y

example723 : (n : ℕ) → n ≅ 0 mod n
example723 = λ n → pair 1 ((ℕ.*-identityʳ n □ sym (dist-lemma₁ n)))

prop724a : (k n : ℕ) → n ≅ n mod k
prop724a = λ k n → pair 0 (ℕ.*-zeroʳ k □ sym (dist-lemma₃ n))

lemma724b : (m n : ℕ) → distℕ m n ≡ distℕ n m
lemma724b = λ m → indℕ (λ m → (n : ℕ) → distℕ m n ≡ distℕ n m)
                       (λ n → dist-lemma₁′ n □ sym (dist-lemma₁ n))
                       (λ m′ outer n → indℕ (λ n → distℕ (suc m′) n ≡ distℕ n (suc m′))
                                            refl
                                            (λ n′ inner → dist-lemma₂ m′ n′ □ (outer n′ □ sym (dist-lemma₂ n′ m′)))
                                            n)
                       m


prop724b : (k m n : ℕ) → m ≅ n mod k → n ≅ m mod k
prop724b = λ k m n m≅n → indΣ (λ _ → n ≅ m mod k)
                              (λ x q → pair x (q □ lemma724b m n))
                              m≅n

-- prop724c' : (m n o k : ℕ) → m ≅ n mod k → n ≅ o mod k → m ≅ o mod k
-- prop724c' m n o k (q₁ , eq₁) (q₂ , eq₂) = {!!} , {!!}

-- prop724c : (m n o k : ℕ) → m ≅ n mod k → n ≅ o mod k → m ≅ o mod k
-- prop724c = λ m n o k m≅n n≅o → {!!}

--------------------------------------------------------------------------------
-- §7 finite types
--
-- Potential name clash here...

-- Erm, am I supposed to be using this definition?

_<_ : ℕ → ℕ → Set
_<_ = indℕ (λ _ → ℕ → Set)
        (λ n → indℕ (λ _ → Set) ∅ (λ _ _ → 𝟙) n)
        λ m′ outer → indℕ (λ _ → Set) ∅ λ n′ _ → outer n′

blah-zero : zero < zero ≡ ∅
blah-zero = refl

blah : ∀ b → (zero < (suc b) ≡ 𝟙)
blah = λ b → refl


classical-Fin : ℕ → Set
classical-Fin = λ k → Σ[ x ∈ ℕ ] x < k

Fin : ℕ → Set
Fin = indℕ (λ _ → Set) ∅ (λ _ ih → ih ⊎ 𝟙)

-- Constructors...?

ind-Fin : (P : (k : ℕ) (x : Fin k) → Set) →
          ((k : ℕ) → P (suc k) (inr ⋆)) →
          ((k : ℕ) (x : Fin k) → P k x → P (suc k) (inl x)) →
          (k : ℕ) → (x : Fin k) → P k x
ind-Fin = λ P gₖ pₖ → indℕ (λ k → (x : Fin k) → P k x)
                          (λ x → ex-falso x)
                          (λ n′ ih → ind⊎ (P (suc n′)) (λ x → pₖ n′ x (ih x)) (λ y → ind𝟙 (λ y → P (suc n′) (inr y)) (gₖ n′) y))

ι : (k : ℕ) → Fin k → ℕ
ι = ind-Fin (λ k x → ℕ) id (λ _ _ → id)

ι′ : (k : ℕ) → Fin k → ℕ
ι′ = ind-Fin (λ _ _ → ℕ) (λ _ → 0) (λ _ _ → suc)

_ : ι′ 3 (inr ⋆) ≡ 0
_ = refl

_ : ι′ 3 (inl (inr ⋆)) ≡ 1
_ = refl

-- Lemma 7.3.5

test1 : ι 3 (inl (inl (inr ⋆))) ≡ 0
test1 = refl

test2 : ι 3 (inl (inr ⋆)) ≡ 1
test2 = refl

test3 : ι 3 (inr ⋆) ≡ 2
test3 = refl

k<k+1 : (k : ℕ) → k < suc k
k<k+1 = indℕ (λ k → k < suc k) ⋆ (λ k′ ih → ih)

<-trans : (a b c : ℕ) → a < b → b < c → a < c
<-trans = indℕ (λ a → (b c : ℕ) → a < b → b < c → a < c)
               (indℕ (λ b → (c : ℕ) → 0 < b → b < c → 0 < c)
                     (indℕ (λ c → 0 < 0 → 0 < c → 0 < c)
                           (λ a<b b<c → a<b)
                           (λ _ _ _ → id))
                     λ b′ ih → indℕ (λ c → 0 < suc b′ → suc b′ < c → 0 < c)
                                    (λ _ → id)
                                    λ _ _ _ _ → ⋆)
               λ a′ ih → indℕ (λ b → (c : ℕ) → suc a′ < b → b < c → suc a′ < c)
                              (λ _ → ex-falso)
                              (λ b′ _ → indℕ (λ c → suc a′ < suc b′ → suc b′ < c → suc a′ < c)
                                             (λ _ → ex-falso)
                                             (λ c′ _ q₁ q₂ → ih b′ c′ q₁ q₂))

lemma735′ : (k : ℕ) (x : Fin k) → ι k x < k
lemma735′ (suc k) (inl x) = <-trans (ι k x) k (suc k) (lemma735′ k x) (k<k+1 k)
lemma735′ (suc k) (inr ⋆) = k<k+1 k

lemma735 : (k : ℕ) (x : Fin k) → ι k x < k
lemma735 = ind-Fin (λ k x → ι k x < k)
                   (λ k → k<k+1 k)
                   (λ k x ih → <-trans (ι k x) k (suc k) ih (k<k+1 k))

lem : (k : ℕ) → (z : Fin k) → ι (suc k) (inl z) < k
lem (suc k) (inl x) =
  let ih = lem k x in
  {!   !}
lem (suc k) (inr ⋆) = {!   !}

lemF : ∀ k x → ι (suc k) (inl x) ≡ ι (suc k) (inr ⋆) → ∅
lemF = {!   !}

lemG : ∀ k x → ι (suc k) (inr ⋆) ≡ ι (suc k) (inl x) → ∅
lemG = {!   !}

ι-injective′ : (k : ℕ) → (x y : Fin k) → ι k x ≡ ι k y → x ≡ y
ι-injective′ (suc k) (inl x) (inl y) q =
  let q′ = ι-injective′ k x y
  in ap inl x y (q′ q)
ι-injective′ (suc k) (inl x) (inr ⋆) q = ex-falso (lemF _ _ q)
ι-injective′ (suc k) (inr ⋆) (inl x) q = ex-falso (lemG _ _ q)
ι-injective′ (suc k) (inr ⋆) (inr ⋆) q = refl

ι-injective : (k : ℕ) → (x y : Fin k) → ι k x ≡ ι k y → x ≡ y
ι-injective = ind-Fin (λ k x → (y : Fin k) → ι k x ≡ ι k y → x ≡ y)
                      (λ k y → ind-Fin (λ k′ y′ → {!   !})
                                       {!   !}
                                       {!   !}
                                       (suc k) y)
                      {!   !}
